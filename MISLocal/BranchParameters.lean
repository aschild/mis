import MISLocal.FrequentLabels

/-! Explicit real inequalities for the independent-list argument.
There are no natural-number floors, subtractions, or asymptotic hypotheses. -/

namespace MISLocal
noncomputable section

theorem exp_neg_nat_log {D : ℝ} (hD : 0 < D) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log D) = 1 / D^n := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hD, one_div]

theorem branch_parameter_estimates {D ell M C ν t : ℝ}
    (hD : 12 ≤ D) (hlog : 1 ≤ Real.log D) (hM : 0 < M)
    (hellM : 32*ell ≤ M) (hC0 : 0 ≤ C) (hC : C ≤ ell*ν)
    (hCmax : C ≤ D^4) (hν : 256*Real.log D ≤ ν) (ht : 1/D ≤ t) :
    1 ≤ ν/8 ∧ Real.exp (-ν/128) ≤ t/12 ∧
      4*C*Real.exp (2*C/M-ν/8) ≤ t/8 := by
  have hDp : 0 < D := by linarith
  have hν0 : 0 ≤ ν := by linarith
  have hsmall : Real.exp (-ν/128) ≤ 1/D^2 := by
    calc
      _ ≤ Real.exp (-(2:ℝ)*Real.log D) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := exp_neg_nat_log hDp 2
  have hDsmall : (1:ℝ)/D^2 ≤ (1/D)/12 := by
    calc
      _ ≤ 1/(12*D) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ = _ := by ring
  have hCM : 2*C/M ≤ ν/16 := by
    apply (div_le_iff₀ hM).mpr
    nlinarith [mul_le_mul_of_nonneg_right hellM hν0]
  have hexp : Real.exp (2*C/M-ν/8) ≤ 1/D^16 := by
    calc
      _ ≤ Real.exp (-(16:ℝ)*Real.log D) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := exp_neg_nat_log hDp 16
  have hpow : (32:ℝ) ≤ D^11 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (show (2:ℝ) ≤ D by linarith) 11
    norm_num at h
    linarith
  have hlarge : 4*D^4/D^16 ≤ 1/(8*D) := by
    apply (div_le_div_iff₀ (pow_pos hDp 16) (by positivity : 0 < 8*D)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hpow (pow_nonneg hDp.le 5)]
  refine ⟨by linarith, hsmall.trans (hDsmall.trans (by linarith)), ?_⟩
  calc
    _ ≤ 4*C*(1/D^16) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 4*D^4/D^16 := by
      simpa [div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCmax (by norm_num : (0:ℝ) ≤ 4))
          (inv_nonneg.mpr (pow_nonneg hDp.le 16))
    _ ≤ 1/(8*D) := hlarge
    _ ≤ t/8 := by rw [show (1:ℝ)/(8*D) = (1/D)/8 by ring]; linarith

end
end MISLocal
