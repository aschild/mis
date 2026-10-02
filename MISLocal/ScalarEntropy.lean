import MISLocal.EntropyProduct

/-! Scalar neighboring-output estimate from an edge/vertex entropy inequality. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def binaryEntropy (p : ℝ) : ℝ := Real.negMulLog p + Real.negMulLog (1-p)

theorem binaryEntropy_le_rare {p : ℝ} (hp : p ≤ 1) :
    binaryEntropy p ≤ p + Real.negMulLog p := by
  have h := negMulLog_tangent (show 0 ≤ 1-p by linarith) (by norm_num : (0:ℝ) < 1)
  simp only [Real.log_one, mul_zero] at h
  unfold binaryEntropy
  linarith

theorem binaryEntropy_le_two_log {p D : ℝ}
    (hD : 0 < D) (hlog : 1 ≤ Real.log D) (hp : 1/D ≤ p) (hp1 : p ≤ 1) :
    binaryEntropy p ≤ 2*p*Real.log D := by
  have hpp : 0 < p := lt_of_lt_of_le (one_div_pos.mpr hD) hp
  have hpl := Real.log_le_log (one_div_pos.mpr hD) hp
  simp only [one_div, Real.log_inv] at hpl
  have h := binaryEntropy_le_rare hp1
  simp only [Real.negMulLog] at h
  nlinarith [mul_le_mul_of_nonneg_left hpl hpp.le,
    mul_le_mul_of_nonneg_left hlog hpp.le]

namespace FiniteProb

variable {Ω : Type*} [Fintype Ω]

theorem bool_entropy (P : FiniteProb Bool) : P.entropy = binaryEntropy (P.weight true) := by
  have ht := P.total
  simp only [Fintype.sum_bool] at ht
  have hf : P.weight false = 1-P.weight true := by linarith
  simp [entropy, Fintype.sum_bool, binaryEntropy, hf, add_comm]

theorem scalar_pair_overlap (μ : FiniteProb Ω) (U V : Ω → Bool) {D p : ℝ}
    (hD : 0 < D) (hu : μ.prob (fun ω => U ω = true) = p)
    (hv : μ.prob (fun ω => V ω = true) = p)
    (htree : (D/2)*μ.entropyOf (fun ω => (U ω,V ω)) ≥ (D-1)*μ.entropyOf U) :
    p^2/2 - 2*binaryEntropy p/D ≤ μ.prob (fun ω => U ω = true ∧ V ω = true) := by
  let P := μ.map (fun ω => (U ω,V ω))
  let Q := (μ.map U).product (μ.map V)
  have hhu : μ.entropyOf U = binaryEntropy p := by
    change (μ.map U).entropy = _
    rw [bool_entropy]
    exact congrArg binaryEntropy hu
  have hhv : μ.entropyOf V = binaryEntropy p := by
    change (μ.map V).entropy = _
    rw [bool_entropy]
    exact congrArg binaryEntropy hv
  have hkl : P.kl Q ≤ 2*binaryEntropy p/D := by
    rw [show P.kl Q = μ.entropyOf U + μ.entropyOf V - μ.entropyOf (fun ω => (U ω,V ω)) from
      μ.kl_marginalProduct U V, hhu, hhv]
    rw [hhu] at htree
    apply (le_div_iff₀ hD).mpr
    nlinarith
  have hQ : Q.prob (fun ab => ab.1 = true ∧ ab.2 = true) = p^2 := by
    change ((μ.map U).product (μ.map V)).prob _ = _
    simp only [prob, expect, product, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [bit, Bool.false_eq_true, false_and, true_and, and_false,
      if_false, if_true, mul_zero, mul_one, add_zero, zero_add]
    change μ.prob (fun ω => U ω = true) * μ.prob (fun ω => V ω = true) = _
    rw [hu, hv, pow_two]
  have he := P.event_le_two_mul_add_kl Q (μ.dominated_marginalProduct U V)
    (fun ab => ab.1 = true ∧ ab.2 = true)
  rw [hQ] at he
  have hP : P.prob (fun ab => ab.1 = true ∧ ab.2 = true) =
      μ.prob (fun ω => U ω = true ∧ V ω = true) := μ.prob_map _ _
  rw [hP] at he
  linarith

end FiniteProb
end
end MISLocal
