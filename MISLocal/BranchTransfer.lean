import MISLocal.ListCapture
import MISLocal.BranchParameters

/-!
# Relative branch transfer

This proves the independent-branch lemma for actual conditional probabilities.
The output is arbitrary and may be coupled to every input. Eligibility and
the maximizing lists are constructed, rather than supplied as premises.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω I A B : Type*} [Fintype Ω] [Fintype I] [Fintype A] [Fintype B]

def branchEligible (μ : FiniteProb Ω) (X : I → Ω → B) (Z : Ω → Option A)
    (ell : ℕ) (t : ℝ) (i : I) (b : B) : Prop :=
  ((μ.given (X i) b).map Z).tail ell < t/2

def branchList (μ : FiniteProb Ω) (X : I → Ω → B) (Z : Ω → Option A)
    (ell : ℕ) (t : ℝ) (i : I) (b : B) : Finset A :=
  if μ.branchEligible X Z ell t i b then ((μ.given (X i) b).map Z).outputList ell else ∅

omit [Fintype Ω] [Fintype A] in
theorem not_listCaptures_iff (Z : Ω → Option A) (L : Ω → Finset A) (ω : Ω) :
    ¬ listCaptures Z L ω ↔ ∃ a, Z ω = some a ∧ a ∉ L ω := by
  cases h : Z ω <;> simp [listCaptures, h]

omit [Fintype I] in
theorem branch_miss_probability (μ : FiniteProb Ω) (X : I → Ω → B)
    (Z : Ω → Option A) (ell : ℕ) (t : ℝ) (i : I) :
    μ.prob (fun ω => μ.branchEligible X Z ell t i (X i ω) ∧
      ¬ listCaptures Z (fun ω => μ.branchList X Z ell t i (X i ω)) ω) ≤
      t/2 * μ.prob (fun ω => μ.branchEligible X Z ell t i (X i ω)) := by
  let eligible := μ.branchEligible X Z ell t i
  let lists := μ.branchList X Z ell t i
  have hind : μ.prob (fun ω => eligible (X i ω) ∧
      ∃ a, Z ω = some a ∧ a ∉ lists (X i ω)) =
      ∑ b, (μ.map (X i)).weight b * (μ.given (X i) b).prob
        (fun ω => eligible b ∧ ∃ a, Z ω = some a ∧ a ∉ lists b) :=
    (μ.prob_indexed_conditioning (X i)
      (fun b ω => eligible b ∧ ∃ a, Z ω = some a ∧ a ∉ lists b)).symm
  simp_rw [not_listCaptures_iff]
  change μ.prob (fun ω => eligible (X i ω) ∧ ∃ a, Z ω = some a ∧ a ∉ lists (X i ω)) ≤ _
  rw [hind]
  have hpoint (b : B) : (μ.given (X i) b).prob
      (fun ω => eligible b ∧ ∃ a, Z ω = some a ∧ a ∉ lists b) ≤ t/2 * bit (eligible b) := by
    by_cases hb : eligible b
    · simp only [hb, true_and, bit, if_true, mul_one]
      have hl : lists b = ((μ.given (X i) b).map Z).outputList ell := by
        simp only [lists, branchList, show μ.branchEligible X Z ell t i b from hb, if_true]
      rw [hl, ← (μ.given (X i) b).prob_map Z
        (fun z => ∃ a, z = some a ∧ a ∉ ((μ.given (X i) b).map Z).outputList ell),
        ← listTail_prob]
      exact le_of_lt hb
    · simp [hb, bit]
  calc
    _ ≤ ∑ b, (μ.map (X i)).weight b * (t/2 * bit (eligible b)) :=
      Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hpoint b) ((μ.map (X i)).nonneg b))
    _ = _ := by
      change (μ.map (X i)).expect (fun b => t/2 * bit (eligible b)) = _
      rw [expect_mul, ← prob, prob_map]

theorem branchList_total_weight (μ : FiniteProb Ω) (X : I → Ω → B)
    (Z : Ω → Option A) (ell : ℕ) (t : ℝ) :
    μ.totalListWeight (fun i ω => μ.branchList X Z ell t i (X i ω)) ≤
      (ell : ℝ) * μ.eventMean (fun i ω => μ.branchEligible X Z ell t i (X i ω)) := by
  rw [μ.totalListWeight_eq]
  have hcard (i : I) (ω : Ω) :
      ((μ.branchList X Z ell t i (X i ω)).card : ℝ) ≤
        (ell : ℝ) * bit (μ.branchEligible X Z ell t i (X i ω)) := by
    by_cases h : μ.branchEligible X Z ell t i (X i ω)
    · simp only [branchList, h, if_true, bit, mul_one]
      exact_mod_cast bestList_card (fun a => ((μ.given (X i) (X i ω)).map Z).weight (some a)) ell
    · simp [branchList, h, bit]
  calc
    _ ≤ ∑ i, μ.expect (fun ω => (ell : ℝ) * bit (μ.branchEligible X Z ell t i (X i ω))) :=
      Finset.sum_le_sum (fun i _ => μ.expect_mono (hcard i))
    _ = _ := by simp only [μ.expect_mul, ← Finset.mul_sum, eventMean, prob]

/-- The expected number of unusually informative branches is at most
`256 log D`. Dividing by `D` gives the uniform-direction probability bound.
All size assumptions are numerical and explicit. -/
theorem branch_transfer (μ : FiniteProb Ω) (X : I → Ω → B) (Z : Ω → Option A)
    (hind : μ.Independent X) (ell M : ℕ)
    (hD : 12 ≤ (Fintype.card I : ℝ)) (hlog : 1 ≤ Real.log (Fintype.card I : ℝ))
    (hM : 0 < M) (hellM : 32 * ell ≤ M)
    (hsize : (M : ℝ) * Fintype.card I ≤ (Fintype.card I : ℝ)^4)
    (ht : 1/(Fintype.card I : ℝ) ≤ (μ.map Z).tail M) :
    (∑ i, μ.prob (fun ω => ((μ.given (X i) (X i ω)).map Z).tail ell < (μ.map Z).tail M/2)) ≤
      256 * Real.log (Fintype.card I : ℝ) := by
  let D : ℝ := Fintype.card I
  let t := (μ.map Z).tail M
  let E : I → Ω → Prop := fun i ω => μ.branchEligible X Z ell t i (X i ω)
  let L : I → Ω → Finset A := fun i ω => μ.branchList X Z ell t i (X i ω)
  let ν := μ.eventMean E
  let C := μ.totalListWeight L
  let S := bestList (μ.labelWeight L) M
  change ν ≤ 256*Real.log D
  by_contra h
  have hν : 256*Real.log D ≤ ν := (lt_of_not_ge h).le
  have hν0 : (0:ℝ) < ν := by dsimp [D] at hν; linarith
  have hDp : 0 < D := by dsimp [D]; linarith
  have ht0 : 0 < t := lt_of_lt_of_le (one_div_pos.mpr hDp) ht
  have hνD : ν ≤ D := by
    calc
      _ ≤ ∑ _i : I, (1:ℝ) := Finset.sum_le_sum (fun i _ => μ.prob_le_one (E i))
      _ = _ := by simp [D]
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun a _ => μ.eventMean_nonneg (fun i ω => a ∈ L i ω))
  have hC : C ≤ (ell:ℝ)*ν := μ.branchList_total_weight X Z ell t
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hellM' : (32:ℝ)*ell ≤ M := by exact_mod_cast hellM
  have hellM'' : (ell:ℝ) ≤ M := by nlinarith [show (0:ℝ) ≤ ell by positivity]
  have hCmax : C ≤ D^4 := by
    have hc1 := mul_le_mul_of_nonneg_left hνD (Nat.cast_nonneg ell)
    have hc2 := mul_le_mul_of_nonneg_right hellM'' hDp.le
    change (M:ℝ)*D ≤ D^4 at hsize
    linarith
  obtain ⟨ha, hsmall, hfreq⟩ := branch_parameter_estimates hD hlog hM' hellM' hC0 hC hCmax hν ht
  have hcap := μ.many_eligible_captures E (fun i => listCaptures Z (L i))
    (hind.events (μ.branchEligible X Z ell t))
    (fun i => μ.branch_miss_probability X Z ell t i) hsmall hν0
  have hfrequent := (μ.frequent_label_bound L (hind.comp (μ.branchList X Z ell t)) hM ha).trans hfreq
  have hfixed := μ.fixed_list_from_many_captures Z L E S (ν/8) hcap hfrequent
  have htail : t ≤ (μ.map Z).listTail S := (μ.map Z).tail_minimal M S (bestList_card _ _)
  linarith

end FiniteProb
end
end MISLocal
