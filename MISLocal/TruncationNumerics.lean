import MISLocal.ScalarEntropy

/-! Numerical solution of the truncation moment inequality. -/

namespace MISLocal
noncomputable section

theorem quadratic_upper_bound {x b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x^2 ≤ b*x+c^2) : x ≤ b+c := by
  by_contra hn
  have hp := lt_of_not_ge hn
  have hprod := mul_pos (sub_pos.mpr hp) (show 0 < x+c by linarith)
  nlinarith [mul_nonneg hb hc]

theorem truncation_moment_bound {D μ τ w q : ℝ}
    (hD : 0 < D) (hlog : 1 ≤ Real.log D) (hμ1 : μ ≤ 1)
    (hw : 0 ≤ w) (hq : q ≤ 1/D^2) (hmass : τ ≤ 2*μ+2/D)
    (hmoment : μ^2/2 - 2*binaryEntropy μ/D ≤ 4*w+q+2*(256*Real.log D/D)*μ) :
    τ ≤ 2100*Real.log D/D + 6*Real.sqrt w := by
  have hinv : 0 < 1/D := one_div_pos.mpr hD
  have hbase : 1/D ≤ Real.log D/D := div_le_div_of_nonneg_right hlog hD.le
  have hs := Real.sqrt_nonneg w
  by_cases hμ : 1/D ≤ μ
  · have hent := binaryEntropy_le_two_log hD hlog hμ hμ1
    have he := div_le_div_of_nonneg_right hent hD.le
    have hquad : μ^2 ≤ (1032*Real.log D/D)*μ + 8*w+2*q := by
      simp only [div_eq_mul_inv] at hmoment he ⊢
      nlinarith
    have hs2 := Real.sq_sqrt hw
    have hinv2 : (1/D)^2 = (1:ℝ)/D^2 := by ring
    have hc : 8*w+2*q ≤ (3*Real.sqrt w+2/D)^2 := by
      simp only [div_eq_mul_inv, ← inv_pow, one_mul] at hq ⊢
      nlinarith [mul_nonneg hs (inv_nonneg.mpr hD.le), sq_nonneg D⁻¹]
    have hμbound := quadratic_upper_bound
      (show 0 ≤ 1032*Real.log D/D by positivity)
      (show 0 ≤ 3*Real.sqrt w+2/D by positivity) (hquad.trans (by linarith))
    simp only [div_eq_mul_inv] at hμbound hmass hbase hinv ⊢
    nlinarith
  · have hμ' := le_of_not_ge hμ
    simp only [div_eq_mul_inv] at hμ' hmass hbase hinv ⊢
    nlinarith

end
end MISLocal
