import MISLocal.SymmetryTransport
import MISLocal.WeightedBranch
import MISLocal.ParentCharging

/-! Homogeneity is stated as measure-preserving input relabelings that
intertwine outputs and views. It contains no entropy or occupancy inequalities.
Every ancestor restriction inherits these actual relabeling identities. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def endpoint {V E : Type*} (left right : E → V) (e : E) (b : Bool) : V :=
  if b then right e else left e

structure EndpointTransport {Ω V E A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (μ : FiniteProb Ω) (U : V → Ω → Option A) (W : ℕ → V → Ω → B) (F : ℕ → E → Ω → B)
    (left right : E → V) (s t : E × Bool) where
  input : Ω → Ω
  preserves : μ.map input = μ
  firstView : ℕ → B ≃ B
  secondView : ℕ → B ≃ B
  sharedView : ℕ → B ≃ B
  outputFirst : ∀ ω, U (endpoint left right t.1 t.2) (input ω) = U (endpoint left right s.1 s.2) ω
  outputSecond : ∀ ω, U (endpoint left right t.1 (!t.2)) (input ω) = U (endpoint left right s.1 (!s.2)) ω
  viewFirst : ∀ j ω, W j (endpoint left right t.1 t.2) (input ω) =
    firstView j (W j (endpoint left right s.1 s.2) ω)
  viewSecond : ∀ j ω, W j (endpoint left right t.1 (!t.2)) (input ω) =
    secondView j (W j (endpoint left right s.1 (!s.2)) ω)
  viewShared : ∀ j ω, F j t.1 (input ω) = sharedView j (F j s.1 ω)

def ViewHomogeneous {Ω V E A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (μ : FiniteProb Ω) (U : V → Ω → Option A) (W : ℕ → V → Ω → B) (F : ℕ → E → Ω → B)
    (left right : E → V) : Prop :=
  ∀ s t : E × Bool, Nonempty (EndpointTransport μ U W F left right s t)

namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem occupancyScalar_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : Ω → B) (β : B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ ω, Y' (e ω) = β (Y ω)) (D : ℝ) (ω : Ω) :
    μ.occupancyScalar U' Y' D (Y' (e ω)) = μ.occupancyScalar U Y D (Y ω) := by
  rw [hY]
  unfold occupancyScalar
  rw [← (μ.given Y' (β (Y ω))).prob_map U' (fun x => x ≠ none),
    μ.given_map_transport e he U U' Y Y' β hU hY, prob_map]

end FiniteProb

namespace ViewHomogeneous

variable {Ω V E A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    {μ : FiniteProb Ω} {U : V → Ω → Option A} {W : ℕ → V → Ω → B} {F : ℕ → E → Ω → B}
    {left right : E → V}

theorem survivor (h : ViewHomogeneous μ U W F left right) (m n : ℕ) :
    ViewHomogeneous μ (fun v => μ.survivor (U v) (fun j => W (j+1) v) m n) W F left right := by
  intro s t
  obtain ⟨a⟩ := h s t
  exact ⟨{ a with
    outputFirst := μ.survivor_transport a.input a.preserves _ _ _ _ (fun j => a.firstView (j+1))
      a.outputFirst (fun j => a.viewFirst (j+1)) m n
    outputSecond := μ.survivor_transport a.input a.preserves _ _ _ _ (fun j => a.secondView (j+1))
      a.outputSecond (fun j => a.viewSecond (j+1)) m n }⟩

theorem firstDeleted (h : ViewHomogeneous μ U W F left right) (m n : ℕ) :
    ViewHomogeneous μ (fun v => μ.firstDeleted (U v) (fun j => W (j+1) v) m n) W F left right := by
  intro s t
  obtain ⟨a⟩ := h s t
  exact ⟨{ a with
    outputFirst := μ.firstDeleted_transport a.input a.preserves _ _ _ _ (fun j => a.firstView (j+1))
      a.outputFirst (fun j => a.viewFirst (j+1)) m n
    outputSecond := μ.firstDeleted_transport a.input a.preserves _ _ _ _ (fun j => a.secondView (j+1))
      a.outputSecond (fun j => a.viewSecond (j+1)) m n }⟩

theorem scalar_pair_moment (h : ViewHomogeneous μ U W F left right) (j : ℕ) (D : ℝ)
    (e e' : E) :
    μ.expect (fun ω => μ.occupancyScalar (U (left e')) (W j (left e')) D (W j (left e') ω) *
      μ.occupancyScalar (U (right e')) (W j (right e')) D (W j (right e') ω)) =
    μ.expect (fun ω => μ.occupancyScalar (U (left e)) (W j (left e)) D (W j (left e) ω) *
      μ.occupancyScalar (U (right e)) (W j (right e)) D (W j (right e) ω)) := by
  obtain ⟨a⟩ := h (e,false) (e',false)
  rw [← μ.expect_invariant a.input a.preserves]
  apply μ.expect_congr
  intro ω
  have h1 := μ.occupancyScalar_transport a.input a.preserves _ _ _ _ (a.firstView j)
    a.outputFirst (a.viewFirst j) D ω
  have h2 := μ.occupancyScalar_transport a.input a.preserves _ _ _ _ (a.secondView j)
    a.outputSecond (a.viewSecond j) D ω
  simpa only [endpoint, Bool.not_false, Bool.false_eq_true, if_false, if_true] using congrArg₂ (·*·) h1 h2

theorem scalar_mean (h : ViewHomogeneous μ U W F left right) (j : ℕ) (D : ℝ)
    (e₀ : E) (v : V) (hcover : ∃ e b, endpoint left right e b = v) :
    μ.expect (fun ω => μ.occupancyScalar (U v) (W j v) D (W j v ω)) =
      μ.expect (fun ω => μ.occupancyScalar (U (left e₀)) (W j (left e₀)) D (W j (left e₀) ω)) := by
  obtain ⟨e,b,rfl⟩ := hcover
  obtain ⟨a⟩ := h (e₀,false) (e,b)
  rw [← μ.expect_invariant a.input a.preserves]
  apply μ.expect_congr
  intro ω
  exact μ.occupancyScalar_transport a.input a.preserves _ _ _ _ (a.firstView j)
    a.outputFirst (a.viewFirst j) D ω

theorem weighted_failure_equal (h : ViewHomogeneous μ U W F left right)
    (j : ℕ) (D : ℝ) (ell : ℕ) (v : V) (e e' : E)
    (hv : edgeIncident left right v e) (hv' : edgeIncident left right v e') :
    μ.expect (fun ω => μ.occupancyScalar (U v) (W j v) D (W j v ω) *
      bit (((μ.given (F j e') (F j e' ω)).map (U v)).tail ell <
        μ.occupancyScalar (U v) (W j v) D (W j v ω))) =
    μ.expect (fun ω => μ.occupancyScalar (U v) (W j v) D (W j v ω) *
      bit (((μ.given (F j e) (F j e ω)).map (U v)).tail ell <
        μ.occupancyScalar (U v) (W j v) D (W j v ω))) := by
  have hb : ∃ b, endpoint left right e b = v :=
    hv.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  have hb' : ∃ b, endpoint left right e' b = v :=
    hv'.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  obtain ⟨b,hb⟩ := hb
  obtain ⟨b',hb'⟩ := hb'
  obtain ⟨a⟩ := h (e,b) (e',b')
  have hu : ∀ ω, U v (a.input ω) = U v ω := by simpa only [hb, hb'] using a.outputFirst
  have hy : ∀ ω, W j v (a.input ω) = a.firstView j (W j v ω) := by
    simpa only [hb, hb'] using a.viewFirst j
  rw [← μ.expect_invariant a.input a.preserves]
  apply μ.expect_congr
  intro ω
  have hs := μ.occupancyScalar_transport a.input a.preserves (U v) (U v) (W j v) (W j v)
    (a.firstView j) hu hy D ω
  have ht := μ.given_map_transport a.input a.preserves (U v) (U v) (F j e) (F j e')
    (a.sharedView j) hu (a.viewShared j) (F j e ω)
  rw [hs, a.viewShared j ω, ht]

theorem output_distribution (h : ViewHomogeneous μ U W F left right)
    (e₀ : E) (v : V) (hcover : ∃ e b, endpoint left right e b = v) :
    μ.map (U v) = μ.map (U (left e₀)) := by
  obtain ⟨e,b,rfl⟩ := hcover
  obtain ⟨a⟩ := h (e₀,false) (e,b)
  exact μ.map_transport a.input a.preserves _ _ a.outputFirst

theorem vertex_conditional_entropy (h : ViewHomogeneous μ U W F left right)
    (j : ℕ) (e₀ : E) (v : V) (hcover : ∃ e b, endpoint left right e b = v) :
    μ.condEntropy (U v) (W j v) = μ.condEntropy (U (left e₀)) (W j (left e₀)) := by
  obtain ⟨e,b,rfl⟩ := hcover
  obtain ⟨a⟩ := h (e₀,false) (e,b)
  exact μ.conditional_entropy_transport a.input a.preserves _ _ _ _ (Equiv.refl _) (a.firstView j)
    a.outputFirst (a.viewFirst j)

theorem edge_conditional_entropy (h : ViewHomogeneous μ U W F left right)
    (j : ℕ) (e₀ e : E) :
    μ.condEntropy (fun ω => (U (left e) ω,U (right e) ω)) (F j e) =
      μ.condEntropy (fun ω => (U (left e₀) ω,U (right e₀) ω)) (F j e₀) := by
  obtain ⟨a⟩ := h (e₀,false) (e,false)
  exact μ.conditional_entropy_transport a.input a.preserves _ _ _ _ (Equiv.refl _) (a.sharedView j)
    (fun ω => Prod.ext (a.outputFirst ω) (a.outputSecond ω)) (a.viewShared j)

end ViewHomogeneous
end
end MISLocal
