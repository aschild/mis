import MISLocal.WeightedBranch
import MISLocal.EndpointTails
import MISLocal.TruncationNumerics

/-! Assembly of the robust one-layer estimate. Failure costs are weighted by
the local occupancy surrogate, so their total is proportional to its mean. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem tails_cover_product {a b x y : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a*b ≤ x*y+a*bit (x<a)+b*bit (y<b) := by
  have hxy := mul_nonneg hx hy
  by_cases ha : x < a
  · have hab := mul_le_mul_of_nonneg_left hb1 ha0
    have hf := mul_nonneg hb0 (bit_nonneg (y<b))
    simp only [bit, ha, if_true, mul_one] at *
    linarith
  · by_cases hb : y < b
    · have hab := mul_le_mul_of_nonneg_right ha1 hb0
      simp only [bit, ha, hb, if_false, if_true, mul_zero, mul_one]
      linarith
    · simp only [bit, ha, hb, if_false, mul_zero, add_zero]
      exact mul_le_mul (le_of_not_gt ha) (le_of_not_gt hb) hb0 hx

namespace FiniteProb

variable {Ω A B C I : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype I]

theorem weighted_branch_at (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : Ω → B) (F : I → Ω → C) (coarse : I → C → B)
    (href : ∀ i ω, Y ω = coarse i (F i ω)) (ell M m : ℕ)
    (hD : 12 ≤ (Fintype.card I : ℝ)) (hlog : 1 ≤ Real.log (Fintype.card I : ℝ))
    (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*Fintype.card I ≤ (Fintype.card I : ℝ)^4)
    (hratio : (M:ℝ)/m = 1/(Fintype.card I : ℝ))
    (hind : ∀ b, 0 < (μ.map Y).weight b → (μ.given Y b).Independent F)
    (hatom : ∀ b, 0 < (μ.map Y).weight b → ∀ a,
      ((μ.given Y b).map U).weight (some a) ≤ 1/(m:ℝ)) (i₀ : I)
    (hsym : ∀ i, μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω) *
      bit (((μ.given (F i) (F i ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) (Y ω))) =
      μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω) *
      bit (((μ.given (F i₀) (F i₀ ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) (Y ω)))) :
    μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω) *
      bit (((μ.given (F i₀) (F i₀ ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) (Y ω))) ≤
      (256*Real.log (Fintype.card I : ℝ)/(Fintype.card I : ℝ)) *
        μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω)) := by
  have h := μ.weighted_branch_failures U Y F coarse href ell M m hD hlog hM hm hellM hsize hratio hind hatom
  simp only [hsym, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hd : (0:ℝ) < Fintype.card I := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem expected_product_from_tails (μ : FiniteProb Ω) (f g x y : Ω → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hf1 : ∀ ω, f ω ≤ 1)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1)
    (hx : ∀ ω, 0 ≤ x ω) (hy : ∀ ω, 0 ≤ y ω)
    {a b c : ℝ} (htail : μ.expect (fun ω => x ω*y ω) ≤ a)
    (hfail : μ.expect (fun ω => f ω*bit (x ω<f ω)) ≤ b)
    (hfail' : μ.expect (fun ω => g ω*bit (y ω<g ω)) ≤ c) :
    μ.expect (fun ω => f ω*g ω) ≤ a+b+c := by
  have h := μ.expect_mono (fun ω => tails_cover_product (hf0 ω) (hf1 ω) (hg0 ω) (hg1 ω) (hx ω) (hy ω))
  rw [expect_add, expect_add] at h
  linarith

omit [Fintype A] in
/-- Final assembly of one robust truncation step. The tail, branch and scalar
estimates in the premises are the conclusions of separately checked lemmas;
this statement makes their exact interface and constants visible. -/
theorem truncation_from_local_moments (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : Ω → B) (g x y : Ω → ℝ) {D w q : ℝ}
    (hD : 0 < D) (hlog : 1 ≤ Real.log D) (hw : 0 ≤ w) (hq : q ≤ 1/D^2)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1)
    (hx : ∀ ω, 0 ≤ x ω) (hy : ∀ ω, 0 ≤ y ω)
    (htail : μ.expect (fun ω => x ω*y ω) ≤ 4*w+q)
    (hfail : μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω) *
      bit (x ω < μ.occupancyScalar U Y D (Y ω))) ≤
        (256*Real.log D/D)*μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)))
    (hfail' : μ.expect (fun ω => g ω*bit (y ω<g ω)) ≤
        (256*Real.log D/D)*μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)))
    (hscalar : (μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)))^2/2 -
      2*binaryEntropy (μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)))/D ≤
        μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)*g ω)) :
    μ.prob (fun ω => U ω ≠ none) ≤ 2100*Real.log D/D+6*Real.sqrt w := by
  have hup := μ.expected_product_from_tails (fun ω => μ.occupancyScalar U Y D (Y ω)) g x y
    (fun ω => μ.occupancyScalar_nonneg U Y D (Y ω))
    (fun ω => μ.occupancyScalar_le_one U Y hD (Y ω)) hg0 hg1 hx hy htail hfail hfail'
  apply truncation_moment_bound hD hlog
    (μ.expect_le_const (fun ω => μ.occupancyScalar_le_one U Y hD (Y ω))) hw hq
    (μ.occupancyScalar_mass U Y D)
  linarith

end FiniteProb
end
end MISLocal
