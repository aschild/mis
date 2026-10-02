import MISLocal.Repair
import MISLocal.Identifiers

/-!
# Causality of synchronous local computation and legal ID completion

A protocol has unrestricted state/messages and can use its local input each
round. Fixed node/port information can be included in the transition functions.
No symmetry is asserted here; that remains a separate obligation when turning
a concrete LOCAL algorithm into the anonymous edge-input model.

The LOCAL input comprises both an identifier and the tape stored at that
identifier. Thus the completion theorem preserves tapes as well as identifiers.
-/

namespace MISLocal
noncomputable section

def InBall {V : Type*} (G : SimpleGraph V) : ℕ → V → V → Prop
  | 0, v, u => u = v
  | t+1, v, u => u = v ∨ ∃ w, G.Adj v w ∧ InBall G t w u

theorem inBall_self {V : Type*} (G : SimpleGraph V) (t : ℕ) (v : V) : InBall G t v v := by
  cases t <;> simp [InBall]

theorem inBall_mono_succ {V : Type*} (G : SimpleGraph V) (t : ℕ) (v u : V) :
    InBall G t v u → InBall G (t+1) v u := by
  induction t generalizing v u with
  | zero => intro h; exact Or.inl h
  | succ t ih =>
    rintro (h | ⟨w, hvw, hwu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨w, hvw, ih w u hwu⟩

structure LocalProtocol {V : Type*} (G : SimpleGraph V) (Input State : Type*) where
  init : V → Input → State
  step : (t : ℕ) → (v : V) → Input → State → (G.neighborSet v → State) → State

namespace LocalProtocol

variable {V Input State : Type*} {G : SimpleGraph V}

def run (A : LocalProtocol G Input State) (input : V → Input) : ℕ → V → State
  | 0, v => A.init v (input v)
  | t+1, v => A.step t v (input v) (A.run input t v)
      (fun w => A.run input t w.val)

/-- One communication round expands the input-dependence ball by exactly one. -/
theorem run_local (A : LocalProtocol G Input State) (t : ℕ) (v : V)
    (x y : V → Input) (h : ∀ u, InBall G t v u → x u = y u) :
    A.run x t v = A.run y t v := by
  induction t generalizing v with
  | zero => simp only [run, h v (inBall_self G 0 v)]
  | succ t ih =>
    have hv := h v (inBall_self G (t+1) v)
    have hself := ih v (fun u hu => h u (inBall_mono_succ G t v u hu))
    have hn : (fun w : G.neighborSet v => A.run x t w.val) =
        (fun w : G.neighborSet v => A.run y t w.val) := by
      funext w
      apply ih w.val
      intro u hu
      exact h u (Or.inr ⟨w.val, w.property, hu⟩)
    simp only [run, hv, hself, hn]

def candidates (A : LocalProtocol G Input State) (out : V → State → Prop)
    (t : ℕ) (x : V → Input) : Set V := {v | out v (A.run x t v)}

/-- The conflict-removal postprocessing costs one more communication round. -/
theorem repair_local (A : LocalProtocol G Input State) (out : V → State → Prop)
    (t : ℕ) (v : V) (x y : V → Input)
    (h : ∀ u, InBall G (t+1) v u → x u = y u) :
    v ∈ repair G (A.candidates out t x) ↔ v ∈ repair G (A.candidates out t y) := by
  have hself := A.run_local t v x y (fun u hu => h u (inBall_mono_succ G t v u hu))
  have hn (w : V) (hw : G.Adj v w) : A.run x t w = A.run y t w :=
    A.run_local t w x y (fun u hu => h u (Or.inr ⟨w,hw,hu⟩))
  simp only [repair, Set.mem_setOf_eq, candidates, hself]
  constructor
  · rintro ⟨hv, hh⟩
    refine ⟨hv, fun w hw => ?_⟩
    simpa only [← hn w hw] using hh w hw
  · rintro ⟨hv, hh⟩
    refine ⟨hv, fun w hw => ?_⟩
    simpa only [hn w hw] using hh w hw

end LocalProtocol

/-- Local ID uniqueness is sufficient for the entire T-round simulation,
including ID-indexed tapes. Completion outside the ball is irrelevant. -/
theorem completed_ID_simulation {n : ℕ} {Tape State : Type*} (G : SimpleGraph (Fin n))
    (A : LocalProtocol G (Fin n × Tape) State) (t : ℕ) (v : Fin n)
    (ids : Fin n → Fin n) (W : Fin n → Tape)
    (hinj : Set.InjOn ids {u | InBall G t v u}) :
    A.run (fun u => (completeIDs {u | InBall G t v u} ids u,
        W (completeIDs {u | InBall G t v u} ids u))) t v =
      A.run (fun u => (ids u,W (ids u))) t v := by
  apply A.run_local
  intro u hu
  rw [completeIDs_agrees _ ids hinj u hu]

end
end MISLocal
