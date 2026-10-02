import MISLocal.Locality
import MISLocal.GraphViewTransport

/-! A uniform synchronous LOCAL program. The functions receive identifiers,
private tapes, and the identifiers/states at incident ports. They never receive
an underlying vertex name or the entire graph. Giving neighbor identifiers at
time zero only strengthens the model. On a legal ID assignment the neighbors
are distinct, so sorting these IDs supplies a legal port numbering.

States and messages have no size restriction. Sending each whole state is a
full-information simulation of arbitrary port-dependent messages. -/

open scoped Classical
namespace MISLocal
noncomputable section

structure UniformLocalProtocol (n : ℕ) (Tape State : Type*) where
  init : Fin n → Finset (Fin n) → Tape → State
  step : ℕ → Fin n → Tape → State → Finset (Fin n × State) → State
  output : Fin n → State → Bool

namespace UniformLocalProtocol

variable {n : ℕ} {Tape State V : Type*} [Fintype V]
    (A : UniformLocalProtocol n Tape State)

def neighbors (G : SimpleGraph V) (ids : V → Fin n) (v : V) : Finset (Fin n) :=
  (Finset.univ.filter (G.Adj v)).image ids

def run (G : SimpleGraph V) (ids : V → Fin n) (W : Fin n → Tape) : ℕ → V → State
  | 0,v => A.init (ids v) (neighbors G ids v) (W (ids v))
  | t+1,v => A.step t (ids v) (W (ids v)) (run G ids W t v)
      ((Finset.univ.filter (G.Adj v)).image (fun u => (ids u,run G ids W t u)))

def candidates (G : SimpleGraph V) (ids : V → Fin n) (W : Fin n → Tape)
    (t : ℕ) : Set V := {v | A.output (ids v) (A.run G ids W t v) = true}

omit A in
theorem neighbors_eq_of_ids {G : SimpleGraph V} {x y : V → Fin n} {v : V}
    (h : ∀ u, G.Adj v u → x u = y u) : neighbors G x v = neighbors G y v := by
  apply Finset.image_congr
  intro u hu
  exact h u (Finset.mem_filter.mp hu).2

/-- Initialization can read neighbors' IDs. Accordingly a T-round execution
reads only identifiers in the radius-(T+1) ball, including its own tape. -/
theorem run_local (G : SimpleGraph V) (t : ℕ) (v : V)
    (x y : V → Fin n) (W : Fin n → Tape)
    (h : ∀ u, InBall G (t+1) v u → x u = y u) :
    A.run G x W t v = A.run G y W t v := by
  induction t generalizing v with
  | zero =>
    have hv := h v (inBall_self G 1 v)
    have hn : neighbors G x v = neighbors G y v :=
      neighbors_eq_of_ids (fun u hu => h u (Or.inr ⟨u,hu,rfl⟩))
    simp only [run,hv,hn]
  | succ t ih =>
    have hv := h v (inBall_self G (t+1+1) v)
    have hs := ih v (fun u hu => h u (inBall_mono_succ G (t+1) v u hu))
    have hm :
        (Finset.univ.filter (G.Adj v)).image (fun u => (x u,A.run G x W t u)) =
        (Finset.univ.filter (G.Adj v)).image (fun u => (y u,A.run G y W t u)) := by
      apply Finset.image_congr
      intro u hu
      have hvu := (Finset.mem_filter.mp hu).2
      have hid := h u (Or.inr ⟨u,hvu,inBall_self G (t+1) u⟩)
      exact Prod.ext hid (ih u (fun w hw => h w (Or.inr ⟨u,hvu,hw⟩)))
    simp only [run,hv,hs,hm]

theorem candidates_local (G : SimpleGraph V) (t : ℕ) (v : V)
    (x y : V → Fin n) (W : Fin n → Tape)
    (h : ∀ u, InBall G (t+1) v u → x u = y u) :
    v ∈ A.candidates G x W t ↔ v ∈ A.candidates G y W t := by
  have hv := h v (inBall_self G (t+1) v)
  simp only [candidates,Set.mem_setOf_eq,hv,A.run_local G t v x y W h]

/-- The completion may depend on the graph and IDs, but not the tape table. -/
theorem completed_ID_simulation (G : SimpleGraph (Fin n)) (t : ℕ) (v : Fin n)
    (ids : Fin n → Fin n) (W : Fin n → Tape)
    (hinj : Set.InjOn ids {u | InBall G (t+1) v u}) :
    A.run G (completeIDs {u | InBall G (t+1) v u} ids) W t v =
      A.run G ids W t v := by
  apply A.run_local
  intro u hu
  exact completeIDs_agrees _ ids hinj u hu

omit A in
theorem neighborImage_transport {U B : Type*} [Fintype U] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph U) (φ : V ≃ U)
    (v : V) (f : V → B) (g : U → B)
    (hrow : ∀ u, G.Adj v u ↔ H.Adj (φ v) (φ u))
    (hdata : ∀ u, G.Adj v u → f u = g (φ u)) :
    (Finset.univ.filter (G.Adj v)).image f =
      (Finset.univ.filter (H.Adj (φ v))).image g := by
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,huz⟩ := Finset.mem_image.mp hz
    have ha := (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨φ u,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(hrow u).mp ha⟩,(hdata u ha).symm.trans huz⟩
  · intro hz
    obtain ⟨u,hu,huz⟩ := Finset.mem_image.mp hz
    have ha : G.Adj v (φ.symm u) :=
      (hrow (φ.symm u)).mpr (by simpa using (Finset.mem_filter.mp hu).2)
    have hd := hdata (φ.symm u) ha
    rw [φ.apply_symm_apply] at hd
    exact Finset.mem_image.mpr ⟨φ.symm u,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,ha⟩,hd.trans huz⟩

/-- Local graph matching is sufficient; a global graph automorphism is not
needed. Only rows at distance at most T and IDs at distance at most T+1
enter the execution. Both graph and tape data are included. -/
theorem run_transport {U : Type*} [Fintype U] (G : SimpleGraph V) (H : SimpleGraph U) (φ : V ≃ U)
    (ids : V → Fin n) (ids' : U → Fin n) (W : Fin n → Tape) (t : ℕ) (v : V)
    (hids : ∀ u, InBall G (t+1) v u → ids u = ids' (φ u))
    (hrows : ∀ u, InBall G t v u → ∀ w,
      G.Adj u w ↔ H.Adj (φ u) (φ w)) :
    A.run G ids W t v = A.run H ids' W t (φ v) := by
  induction t generalizing v with
  | zero =>
    have hv := hids v (inBall_self G 1 v)
    have hr := hrows v rfl
    have hn : neighbors G ids v = neighbors H ids' (φ v) :=
      neighborImage_transport G H φ v ids ids' hr
        (fun u hu => hids u (Or.inr ⟨u,hu,rfl⟩))
    simp only [run,hv,hn]
  | succ t ih =>
    have hv := hids v (inBall_self G (t+1+1) v)
    have hr := hrows v (inBall_self G (t+1) v)
    have hs := ih v
      (fun u hu => hids u (inBall_mono_succ G (t+1) v u hu))
      (fun u hu => hrows u (inBall_mono_succ G t v u hu))
    have hn :
        (Finset.univ.filter (G.Adj v)).image (fun u => (ids u,A.run G ids W t u)) =
        (Finset.univ.filter (H.Adj (φ v))).image
          (fun u => (ids' u,A.run H ids' W t u)) := by
      apply neighborImage_transport G H φ v _ _ hr
      intro u hu
      refine Prod.ext (hids u (Or.inr ⟨u,hu,inBall_self G (t+1) u⟩)) ?_
      exact ih u (fun w hw => hids w (Or.inr ⟨u,hu,hw⟩))
        (fun w hw => hrows w (Or.inr ⟨u,hu,hw⟩))
    simp only [run,hv,hs,hn]

theorem candidates_transport {U : Type*} [Fintype U] (G : SimpleGraph V) (H : SimpleGraph U) (φ : V ≃ U)
    (ids : V → Fin n) (ids' : U → Fin n) (W : Fin n → Tape) (t : ℕ) (v : V)
    (hids : ∀ u, InBall G (t+1) v u → ids u = ids' (φ u))
    (hrows : ∀ u, InBall G t v u → ∀ w,
      G.Adj u w ↔ H.Adj (φ u) (φ w)) :
    v ∈ A.candidates G ids W t ↔ φ v ∈ A.candidates H ids' W t := by
  have hv := hids v (inBall_self G (t+1) v)
  simp only [candidates,Set.mem_setOf_eq,hv,A.run_transport G H φ ids ids' W t v hids hrows]

end UniformLocalProtocol
end
end MISLocal
