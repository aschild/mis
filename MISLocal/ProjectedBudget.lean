import MISLocal.Projection
import MISLocal.FirstFailure

/-!
# Joint conflict budget for classified parts of an actual zero-conflict output

The parts need not be independent. Their occupied masses sum to the original
occupied mass, each part inherits zero conflict, and direct projection charges
their entropies jointly. The remaining tree-entropy and support-list hypotheses
are spelled out for every part.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def selectedConflict {C A B : Type*} (E : C → A → B → Prop)
    (t : C × Option A × Option B) : Prop :=
  match t.2.1, t.2.2 with
  | some a, some b => E t.1 a b
  | _, _ => False

def classifiedOutput {Ω I A : Type*} (U : Ω → Option A) (classify : Ω → I) (i : I) :
    Ω → Option A := fun ω => if classify ω = i then U ω else none

theorem classified_conflict_subset {Ω I A B C : Type*}
    (U : Ω → Option A) (V : Ω → Option B) (cu cv : Ω → I) (i : I)
    (F : Ω → C) (E : C → A → B → Prop) (ω : Ω) :
    selectedConflict E (F ω, classifiedOutput U cu i ω, classifiedOutput V cv i ω) →
      selectedConflict E (F ω,U ω,V ω) := by
  by_cases hu : cu ω = i <;> by_cases hv : cv ω = i
  · simp [classifiedOutput, hu, hv]
  · cases hU : U ω <;> simp [classifiedOutput, hu, hv, selectedConflict, hU]
  · simp [classifiedOutput, hu, hv, selectedConflict]
  · simp [classifiedOutput, hu, hv, selectedConflict]

namespace FiniteProb

variable {Ω I A B C Y Z : Type*}
  [Fintype Ω] [Fintype I] [Fintype A] [Fintype B] [Fintype C] [Fintype Y] [Fintype Z]

omit [Fintype A] in
theorem classified_occupancy_sum (μ : FiniteProb Ω)
    (U : Ω → Option A) (c : Ω → I) :
    (∑ i, μ.prob (fun ω => classifiedOutput U c i ω ≠ none)) =
      μ.prob (fun ω => U ω ≠ none) := by
  convert μ.classified_mass_sum (fun ω => U ω ≠ none) c using 1
  apply Finset.sum_congr rfl
  intro i _
  apply μ.prob_congr
  intro ω
  by_cases h : c ω = i <;> simp [classifiedOutput, h]

omit [Fintype I] in
theorem classified_zero_conflict (μ : FiniteProb Ω)
    (U : Ω → Option A) (V : Ω → Option B) (cu cv : Ω → I) (i : I)
    (F : Ω → C) (E : C → A → B → Prop)
    (hz : μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) = 0) :
    (μ.map (fun ω => (F ω,classifiedOutput U cu i ω,classifiedOutput V cv i ω))).prob
      (selectedConflict E) = 0 := by
  rw [μ.prob_map]
  apply le_antisymm _ (μ.prob_nonneg _)
  calc
    _ ≤ μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) :=
      μ.prob_mono (classified_conflict_subset U V cu cv i F E)
    _ = 0 := hz

/-- The manuscript's joint first-failure budget, at the finite-distribution level.
The part index has cardinality r. A concrete rule must still supply its smaller
views, short lists, symmetry, and the tree entropy inequality. -/
theorem classified_projected_budget [Nonempty I] (μ : FiniteProb Ω)
    (U : Ω → Option A) (V : Ω → Option B) (cu cv : Ω → I)
    (F : I → Ω → C) (y : I → C → Y) (z : I → C → Z)
    (S : I → Y → Finset A) (E : C → A → B → Prop) {D m p : ℝ}
    (hD : 0 < D) (hm : 1 ≤ m) (hp : p ≤ 1)
    (hmass : μ.prob (fun ω => U ω ≠ none) ≤ p)
    (hzero : ∀ i, μ.prob (fun ω => selectedConflict E (F i ω,U ω,V ω)) = 0)
    (hcard : ∀ i b, ((S i b).card : ℝ) ≤ m)
    (hsupport : ∀ i b, 0 < (μ.map (fun ω => y i (F i ω))).weight b →
      ∀ a, a ∉ S i b →
        ((μ.given (fun ω => y i (F i ω)) b).map (classifiedOutput U cu i)).weight (some a) = 0)
    (hsym : ∀ i, μ.condEntropy (classifiedOutput V cv i) (fun ω => z i (F i ω)) =
      μ.condEntropy (classifiedOutput U cu i) (fun ω => y i (F i ω)))
    (htree : ∀ i, (D-1) * μ.condEntropy (classifiedOutput U cu i) (fun ω => y i (F i ω)) ≤
      D/2 * μ.condEntropy (fun ω => (classifiedOutput U cu i ω,classifiedOutput V cv i ω)) (F i)) :
    (∑ i, (μ.projectedPair (F i) (classifiedOutput U cu i) (classifiedOutput V cv i)
      (y i) (z i)).prob (selectedConflict E)) ≤ 2 * massBudget (m * Fintype.card I) p / D := by
  apply joint_conflict_budget
    (fun i => μ.prob (fun ω => classifiedOutput U cu i ω ≠ none)) _
    hD hm (fun i => μ.prob_nonneg _) hp
  · rw [μ.classified_occupancy_sum]
    exact hmass
  · intro i
    exact μ.direct_projection_rare_bound (F i) (classifiedOutput U cu i)
      (classifiedOutput V cv i) (y i) (z i) (S i) (selectedConflict E)
      hD (lt_of_lt_of_le zero_lt_one hm) (le_refl 0) (hcard i) (hsupport i)
      (hsym i) (by simpa using htree i) (μ.classified_zero_conflict U V cu cv i (F i) E (hzero i))

end FiniteProb
end
end MISLocal
