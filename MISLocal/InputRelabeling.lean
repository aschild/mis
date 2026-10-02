import MISLocal.LocalHomogeneity
import MISLocal.InputGeometry

/-! A concrete sufficient condition for view homogeneity: permute independent
source coordinates and relabel each finite source alphabet. Preservation of
the product distribution and commutation with observed views are proved, so
neither must be supplied as a probabilistic assumption. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

structure InputRelabeling {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] (P : ∀ i, FiniteProb (T i)) where
  coordinate : I ≃ I
  value : ∀ i, T i ≃ T (coordinate i)
  weight : ∀ i a, (P (coordinate i)).weight (value i a) = (P i).weight a

namespace InputRelabeling

variable {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] {P : ∀ i, FiniteProb (T i)}
    (a : InputRelabeling P)

def input : (∀ i, T i) ≃ (∀ i, T i) := a.coordinate.piCongr a.value

def observation : (∀ i, Option (T i)) ≃ (∀ i, Option (T i)) :=
  a.coordinate.piCongr (fun i => Equiv.optionCongr (a.value i))

theorem preserves : (FiniteProb.pi P).map a.input = FiniteProb.pi P := by
  ext x
  rw [FiniteProb.map_equiv_weight]
  change (∏ i, (P i).weight (a.input.symm x i)) = ∏ i, (P i).weight (x i)
  calc
    _ = ∏ i, (P (a.coordinate i)).weight (x (a.coordinate i)) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [input, Equiv.piCongr_symm_apply]
      exact (a.weight i ((a.value i).symm (x (a.coordinate i)))).symm.trans
        (congrArg (P (a.coordinate i)).weight ((a.value i).apply_symm_apply _))
    _ = _ := a.coordinate.prod_comp (fun i => (P i).weight (x i))

theorem observe (S R : Finset I) (h : ∀ i, a.coordinate i ∈ R ↔ i ∈ S)
    (x : ∀ i, T i) : observeInputs R (a.input x) = a.observation (observeInputs S x) := by
  funext j
  obtain ⟨i,rfl⟩ := a.coordinate.surjective j
  simp only [input, observation, Equiv.piCongr_apply_apply, observeInputs, h i]
  by_cases hi : i ∈ S <;> simp [hi]

end InputRelabeling

/-- Ordinary coordinate relabelings suffice for all the distributional
symmetry used in the occupancy argument. Only the algorithm's pointwise
equivariance and the relabeling of its coordinate views remain premises. -/
theorem viewHomogeneous_of_input_relabelings {I V E A : Type*}
    [Fintype I] [DecidableEq I] [Fintype A]
    {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (U : V → (∀ i, T i) → Option A)
    (W : ℕ → V → Finset I) (F : ℕ → E → Finset I) (left right : E → V)
    (a : (E × Bool) → (E × Bool) → InputRelabeling P)
    (hu : ∀ s t ω, U (endpoint left right t.1 t.2) ((a s t).input ω) =
      U (endpoint left right s.1 s.2) ω)
    (hu' : ∀ s t ω, U (endpoint left right t.1 (!t.2)) ((a s t).input ω) =
      U (endpoint left right s.1 (!s.2)) ω)
    (hw : ∀ s t j i, (a s t).coordinate i ∈ W j (endpoint left right t.1 t.2) ↔
      i ∈ W j (endpoint left right s.1 s.2))
    (hw' : ∀ s t j i, (a s t).coordinate i ∈ W j (endpoint left right t.1 (!t.2)) ↔
      i ∈ W j (endpoint left right s.1 (!s.2)))
    (hf : ∀ s t j i, (a s t).coordinate i ∈ F j t.1 ↔ i ∈ F j s.1) :
    ViewHomogeneous (FiniteProb.pi P) U (fun j v => observeInputs (W j v))
      (fun j e => observeInputs (F j e)) left right := by
  intro s t
  exact ⟨{
    input := (a s t).input
    preserves := (a s t).preserves
    firstView := fun _ => (a s t).observation
    secondView := fun _ => (a s t).observation
    sharedView := fun _ => (a s t).observation
    outputFirst := hu s t
    outputSecond := hu' s t
    viewFirst := fun j ω => (a s t).observe _ _ (hw s t j) ω
    viewSecond := fun j ω => (a s t).observe _ _ (hw' s t j) ω
    viewShared := fun j ω => (a s t).observe _ _ (hf s t j) ω }⟩

end
end MISLocal
