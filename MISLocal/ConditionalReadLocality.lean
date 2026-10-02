import MISLocal.ProjectedTails
import MISLocal.InputGeometry

/-! Additional observed coordinates do not change a local output's
conditional distribution when every newly observed coordinate lies outside
its read set. The proof uses actual conditional product independence. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem conditional_product_disjoint_reads {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] (P : ∀ i, FiniteProb (T i))
    (f h : (∀ i, T i) → ℝ) (R S L : Finset I)
    (hf : ReadsOnly f R) (hh : ReadsOnly h S) (hinter : R ∩ S ⊆ L)
    (y : ∀ i, Option (T i)) (hy : 0 < ((pi P).map (observeInputs L)).weight y) :
    ((pi P).given (observeInputs L) y).expect (fun x => f x*h x) =
      ((pi P).given (observeInputs L) y).expect f * ((pi P).given (observeInputs L) y).expect h := by
  have hind := conditional_independent_of_disjoint_reads P
    (fun b : Bool => if b then h else f) (fun b : Bool => if b then S else R) L
    (by intro b; cases b <;> assumption)
    (by
      intro b c hbc i hi hi'
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · exact hinter (Finset.mem_inter.mpr ⟨hi,hi'⟩)
      · exact hinter (Finset.mem_inter.mpr ⟨hi',hi⟩)
      · exact False.elim (hbc rfl)) y hy
  simpa only [Bool.false_eq_true, if_false, if_true, id_eq] using hind.bool_product id id

theorem conditional_reads_irrelevance {I A : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A]
    (P : ∀ i, FiniteProb (T i)) (U : (∀ i, T i) → A) (R S L : Finset I)
    (hU : ReadsOnly U R) (hSL : S ⊆ L) (hinter : R ∩ L ⊆ S)
    (ω : ∀ i, T i) (hω : 0 < (pi P).weight ω) :
    (((pi P).given (observeInputs L) (observeInputs L ω)).map U) =
      (((pi P).given (observeInputs S) (observeInputs S ω)).map U) := by
  let μ := pi P
  let F := observeInputs (T := T) L
  let Y := observeInputs (T := T) S
  have href (x : ∀ i, T i) : Y x = restrictObservation S (F x) :=
    (restrictObservation_observe S L hSL x).symm
  have hF := μ.map_weight_pos F hω
  have hY := μ.map_weight_pos Y hω
  have hc : 0 < ((μ.given Y (Y ω)).map F).weight (F ω) := by
    have he := μ.given_refinement_mass F Y (restrictObservation S) href (F ω)
      (by rwa [← href ω])
    rw [← href ω] at he
    rw [he]
    exact div_pos hF hY
  have hn := μ.given_given_refinement F Y (restrictObservation S) href (F ω) hF
  rw [← href ω] at hn
  rw [← hn]
  ext a
  rw [given_pair_mass _ U F a (F ω) hc]
  have hprod := conditional_product_disjoint_reads P (fun x => bit (U x=a)) (fun x => bit (F x=F ω))
    R L S (by intro x z hxz; exact congrArg (fun u => bit (u=a)) (hU x z hxz))
    (by
      intro x z hxz
      exact congrArg (fun u => bit (u=F ω))
        ((observeInputs_readsOnly L L (Finset.Subset.refl L)) x z hxz))
    hinter (Y ω) hY
  have heq : ((μ.given Y (Y ω)).map (fun x => (U x,F x))).weight (a,F ω) =
      ((μ.given Y (Y ω)).map U).weight a * ((μ.given Y (Y ω)).map F).weight (F ω) := by
    change (μ.given Y (Y ω)).expect (fun x => bit ((U x,F x)=(a,F ω))) = _
    rw [expect_congr _ (fun x => show bit ((U x,F x)=(a,F ω)) = bit (U x=a)*bit (F x=F ω) from by
      by_cases hu : U x=a <;> by_cases hf : F x=F ω <;> simp [bit, Prod.mk.injEq, hu, hf])]
    exact hprod
  rw [heq, mul_div_cancel_right₀ _ (ne_of_gt hc)]

end FiniteProb
end
end MISLocal
