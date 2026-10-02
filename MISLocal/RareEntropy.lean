import MISLocal.EntropyBudget

/-! Entropy bounds for a genuinely small support with an additional empty output. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem sum_negMulLog_support_le {A : Type*} [Fintype A]
    (x : A → ℝ) (hx : ∀ a, 0 ≤ x a) (S : Finset A) {m : ℝ}
    (hm : 0 < m) (hcard : (S.card : ℝ) ≤ m)
    (hsupport : ∀ a, a ∉ S → x a = 0) :
    (∑ a, Real.negMulLog (x a)) ≤
      Real.negMulLog (∑ a, x a) + (∑ a, x a) * Real.log m := by
  let p := ∑ a, x a
  have hp : 0 ≤ p := Finset.sum_nonneg (fun a _ => hx a)
  have hsum : (∑ a ∈ S, x a) = p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha
    exact hsupport a ha
  have hentropy : (∑ a ∈ S, Real.negMulLog (x a)) = ∑ a, Real.negMulLog (x a) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha
    simp [hsupport a ha]
  by_cases hp0 : p = 0
  · have hz (a : A) : x a = 0 := by
      have h := Finset.single_le_sum (fun a _ => hx a) (Finset.mem_univ a)
      change x a ≤ p at h
      exact le_antisymm (hp0 ▸ h) (hx a)
    simp [hz]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have ht := Finset.sum_le_sum (s := S) (fun a _ => negMulLog_tangent (hx a) (div_pos hpp hm))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul, hsum, hentropy] at ht
  have hc := mul_le_mul_of_nonneg_right hcard (le_of_lt (div_pos hpp hm))
  rw [mul_div_cancel₀ _ (ne_of_gt hm)] at hc
  rw [Real.log_div hp0 (ne_of_gt hm)] at ht
  change (∑ a, Real.negMulLog (x a)) ≤ Real.negMulLog p + p * Real.log m
  simp only [Real.negMulLog] at ht ⊢
  nlinarith

namespace FiniteProb

variable {A : Type*} [Fintype A]

theorem occupied_mass (μ : FiniteProb (Option A)) :
    (∑ a, μ.weight (some a)) = μ.prob (fun a => a ≠ none) := by
  simp [prob, expect, Fintype.sum_option, bit]

theorem empty_mass (μ : FiniteProb (Option A)) :
    μ.weight none = 1 - μ.prob (fun a => a ≠ none) := by
  have ht := μ.total
  rw [Fintype.sum_option, μ.occupied_mass] at ht
  linarith

/-- H(Z) ≤ p log(e m / p), with an explicit nonzero support of at most m labels.
Includes p=0, p=1, and the empty support. -/
theorem rare_entropy_le (μ : FiniteProb (Option A)) (S : Finset A) {m : ℝ}
    (hm : 0 < m) (hcard : (S.card : ℝ) ≤ m)
    (hsupport : ∀ a, a ∉ S → μ.weight (some a) = 0) :
    μ.entropy ≤ massBudget m (μ.prob (fun a => a ≠ none)) := by
  have hs := sum_negMulLog_support_le (fun a => μ.weight (some a))
    (fun a => μ.nonneg _) S hm hcard hsupport
  rw [μ.occupied_mass] at hs
  have he := negMulLog_tangent (μ.nonneg none) (show (0:ℝ) < 1 by norm_num)
  simp only [Real.log_one, mul_zero, neg_zero, zero_add, μ.empty_mass] at he
  unfold entropy
  rw [Fintype.sum_option]
  simp only [massBudget]
  rw [μ.empty_mass]
  linarith

end FiniteProb
end
end MISLocal
