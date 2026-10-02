import MISLocal.Entropy

/-!
# Rare-output entropy and the first-failure mass budget

`massBudget m p` is the continuous-at-zero expression `p * log (e*m/p)`.
It is defined as `p * (1 + log m) + negMulLog p`, so its zero case does
not depend on a division convention. The budget for a partition of the
occupied mass is proved here, not postulated as a property of algorithms.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def massBudget (m p : ℝ) : ℝ := p * (1 + Real.log m) + Real.negMulLog p

@[simp] theorem massBudget_zero (m : ℝ) : massBudget m 0 = 0 := by
  simp [massBudget]

theorem massBudget_eq {m p : ℝ} (hm : 0 < m) (hp : 0 < p) :
    massBudget m p = p * Real.log (Real.exp 1 * m / p) := by
  rw [Real.log_div (mul_ne_zero (ne_of_gt (Real.exp_pos _)) (ne_of_gt hm))
    (ne_of_gt hp), Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hm),
    Real.log_exp]
  simp [massBudget, Real.negMulLog]
  ring

/-- A tangent-line proof of the finite entropy bound; zero coordinates are allowed. -/
theorem negMulLog_tangent {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    Real.negMulLog x ≤ -x * Real.log a + a - x := by
  have h := gibbs_term hx (le_of_lt ha) (fun _ => ha)
  simp only [Real.negMulLog]
  nlinarith

/-- Entropy of arbitrary nonnegative masses, without assuming their sum is one. -/
theorem sum_negMulLog_le {I : Type*} [Fintype I] [Nonempty I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, Real.negMulLog (x i)) ≤
      Real.negMulLog (∑ i, x i) + (∑ i, x i) * Real.log (Fintype.card I) := by
  let p := ∑ i, x i
  have hp : 0 ≤ p := Finset.sum_nonneg (fun i _ => hx i)
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  by_cases hp0 : p = 0
  · have hz (i : I) : x i = 0 := by
      have hi := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      change x i ≤ p at hi
      exact le_antisymm (hp0 ▸ hi) (hx i)
    simp [hz]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    negMulLog_tangent (hx i) (div_pos hp' hc))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hs
  change (∑ i, Real.negMulLog (x i)) ≤
    -p * Real.log (p / Fintype.card I) + Fintype.card I * (p / Fintype.card I) - p at hs
  rw [Real.log_div hp0 (ne_of_gt hc), mul_div_cancel₀ _ (ne_of_gt hc)] at hs
  change (∑ i, Real.negMulLog (x i)) ≤ Real.negMulLog p + p * Real.log (Fintype.card I)
  simp only [Real.negMulLog] at hs ⊢
  nlinarith

theorem FiniteProb.entropy_le_log_card {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (μ : FiniteProb Ω) : μ.entropy ≤ Real.log (Fintype.card Ω) := by
  simpa [FiniteProb.entropy, μ.total] using sum_negMulLog_le μ.weight μ.nonneg

/-- The r disjoint first-failure/survivor masses cost only log r, not r. -/
theorem sum_massBudget_le {I : Type*} [Fintype I] [Nonempty I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) {m : ℝ} (hm : 0 < m) :
    (∑ i, massBudget m (x i)) ≤ massBudget (m * Fintype.card I) (∑ i, x i) := by
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs := sum_negMulLog_le x hx
  simp only [massBudget, Finset.sum_add_distrib, ← Finset.sum_mul,
    Real.log_mul (ne_of_gt hm) hc]
  nlinarith

/-- Monotonicity on probability masses, with its scale hypothesis explicit. -/
theorem massBudget_mono {m x y : ℝ} (hm : 1 ≤ m)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : massBudget m x ≤ massBudget m y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  by_cases hyz : y = 0
  · have hxz : x = 0 := le_antisymm (hyz ▸ hxy) hx
    simp [hxz, hyz]
  have hyp : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyz)
  have ht := negMulLog_tangent hx hyp
  have hlogy : Real.log y ≤ 0 := Real.log_nonpos hy0 hy
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hprod : 0 ≤ (y - x) * (Real.log m - Real.log y) :=
    mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (hlogy.trans hlogm))
  simp only [massBudget, Real.negMulLog] at ht ⊢
  nlinarith

/-- Quantitative sum of the individual direct-projection conflict bounds. -/
theorem joint_conflict_budget {I : Type*} [Fintype I] [Nonempty I]
    (x w : I → ℝ) {D m p : ℝ}
    (hD : 0 < D) (hm : 1 ≤ m) (hx : ∀ i, 0 ≤ x i)
    (hp : p ≤ 1) (hmass : ∑ i, x i ≤ p)
    (hw : ∀ i, w i ≤ 2 * massBudget m (x i) / D) :
    (∑ i, w i) ≤ 2 * massBudget (m * Fintype.card I) p / D := by
  have hc : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hm' : 1 ≤ m * Fintype.card I := one_le_mul_of_one_le_of_one_le hm hc
  have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
  have hb := (sum_massBudget_le x hx (lt_of_lt_of_le zero_lt_one hm)).trans
    (massBudget_mono hm' hsum hmass hp)
  calc
    _ ≤ ∑ i, 2 * massBudget m (x i) / D := Finset.sum_le_sum (fun i _ => hw i)
    _ = 2 * (∑ i, massBudget m (x i)) / D := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hD.le

end
end MISLocal
