import MISLocal.NestedGiven

/-! The relative branch estimate, averaged with the local occupancy weight.
This weighted form is essential: an unweighted error would lose the desired
linear dependence on the occupied mass. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C I : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype I]

def occupancyScalar (μ : FiniteProb Ω) (U : Ω → Option A) (Y : Ω → B) (D : ℝ) (b : B) : ℝ :=
  max ((μ.given Y b).prob (fun ω => U ω ≠ none)-2/D) 0 / 2

omit [Fintype A] in
theorem occupancyScalar_nonneg (μ : FiniteProb Ω) (U : Ω → Option A) (Y : Ω → B)
    (D : ℝ) (b : B) : 0 ≤ μ.occupancyScalar U Y D b := by
  exact div_nonneg (le_max_right _ _) (by norm_num)

omit [Fintype A] in
theorem occupancyScalar_le_one (μ : FiniteProb Ω) (U : Ω → Option A) (Y : Ω → B)
    {D : ℝ} (hD : 0 < D) (b : B) : μ.occupancyScalar U Y D b ≤ 1 := by
  have h := (μ.given Y b).prob_le_one (fun ω => U ω ≠ none)
  have hi : 0 < 2/D := div_pos (by norm_num) hD
  unfold occupancyScalar
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  exact max_le (by linarith) (by norm_num)

omit [Fintype A] in
theorem occupancyScalar_mass (μ : FiniteProb Ω) (U : Ω → Option A) (Y : Ω → B) (D : ℝ) :
    μ.prob (fun ω => U ω ≠ none) ≤
      2*μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω))+2/D := by
  have h := (μ.map Y).expect_mono (fun b =>
    show (μ.given Y b).prob (fun ω => U ω ≠ none) ≤ 2*μ.occupancyScalar U Y D b+2/D by
      have h := le_max_left ((μ.given Y b).prob (fun ω => U ω ≠ none)-2/D) 0
      dsimp [occupancyScalar]
      linarith)
  rw [expect_add, expect_mul, expect_const] at h
  have ht := μ.total_conditional_expectation Y (fun ω => bit (U ω ≠ none))
  change (μ.map Y).expect (fun b => (μ.given Y b).prob (fun ω => U ω ≠ none)) =
    μ.prob (fun ω => U ω ≠ none) at ht
  rwa [ht, expect_map] at h

/-- Conditional probability of too-small shared-view tails, in a fixed
positive inner-view fiber. The finer conditioning is proved to agree with
successive conditioning; it is not an extra independence assumption. -/
theorem relative_branch_failures (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : Ω → B) (F : I → Ω → C) (coarse : I → C → B)
    (href : ∀ i ω, Y ω = coarse i (F i ω)) (ell M m : ℕ)
    (hD : 12 ≤ (Fintype.card I : ℝ)) (hlog : 1 ≤ Real.log (Fintype.card I : ℝ))
    (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*Fintype.card I ≤ (Fintype.card I : ℝ)^4)
    (hratio : (M:ℝ)/m = 1/(Fintype.card I : ℝ))
    (b : B) (hb : 0 < (μ.map Y).weight b)
    (hind : (μ.given Y b).Independent F)
    (hatom : ∀ a, ((μ.given Y b).map U).weight (some a) ≤ 1/(m:ℝ))
    (hf : 0 < μ.occupancyScalar U Y (Fintype.card I) b) :
    (∑ i, (μ.given Y b).prob (fun ω =>
      ((μ.given (F i) (F i ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) b)) ≤
      256*Real.log (Fintype.card I : ℝ) := by
  let D : ℝ := Fintype.card I
  have hDp : 0 < D := by dsimp [D]; linarith
  have hlo := (((μ.given Y b).map U)).tail_lower_of_atom_bound M
    (show (0:ℝ) ≤ 1/(m:ℝ) by positivity) hatom
  rw [prob_map, mul_one_div, hratio] at hlo
  have hscalar : μ.occupancyScalar U Y D b =
      ((μ.given Y b).prob (fun ω => U ω ≠ none)-2/D)/2 := by
    unfold occupancyScalar at hf ⊢
    rw [max_eq_left]
    by_contra h
    rw [max_eq_right (le_of_not_ge h)] at hf
    norm_num at hf
  have hp : 2/D < (μ.given Y b).prob (fun ω => U ω ≠ none) := by
    change 0 < μ.occupancyScalar U Y D b at hf
    rw [hscalar] at hf
    linarith
  have ht : 1/D ≤ ((μ.given Y b).map U).tail M := by
    change _ - 1/D ≤ _ at hlo
    simp only [div_eq_mul_inv] at hp hlo ⊢
    linarith
  have hft : μ.occupancyScalar U Y D b ≤ ((μ.given Y b).map U).tail M/2 := by
    rw [hscalar]
    change _ - 1/D ≤ _ at hlo
    have hi : 0 < 1/D := one_div_pos.mpr hDp
    simp only [div_eq_mul_inv] at hlo hi ⊢
    linarith
  have hbranch := (μ.given Y b).branch_transfer F U hind ell M hD hlog hM hellM hsize ht
  apply le_trans _ hbranch
  apply Finset.sum_le_sum
  intro i _
  apply (μ.given Y b).expect_mono_on_support
  intro ω hω
  have he := μ.given_given_at_support (F i) Y (coarse i) (href i) b hb hω
  dsimp only
  rw [he]
  exact bit_mono (fun h => lt_of_lt_of_le h hft)

theorem weighted_branch_failures (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : Ω → B) (F : I → Ω → C) (coarse : I → C → B)
    (href : ∀ i ω, Y ω = coarse i (F i ω)) (ell M m : ℕ)
    (hD : 12 ≤ (Fintype.card I : ℝ)) (hlog : 1 ≤ Real.log (Fintype.card I : ℝ))
    (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*Fintype.card I ≤ (Fintype.card I : ℝ)^4)
    (hratio : (M:ℝ)/m = 1/(Fintype.card I : ℝ))
    (hind : ∀ b, 0 < (μ.map Y).weight b → (μ.given Y b).Independent F)
    (hatom : ∀ b, 0 < (μ.map Y).weight b → ∀ a,
      ((μ.given Y b).map U).weight (some a) ≤ 1/(m:ℝ)) :
    (∑ i, μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω) *
      bit (((μ.given (F i) (F i ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) (Y ω)))) ≤
      256*Real.log (Fintype.card I : ℝ) *
        μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω)) := by
  let f := μ.occupancyScalar U Y (Fintype.card I)
  let fail := fun i ω => ((μ.given (F i) (F i ω)).map U).tail ell < f (Y ω)
  have hpoint (b : B) (hb : 0 < (μ.map Y).weight b) :
      (μ.given Y b).expect (fun ω => ∑ i, f (Y ω)*bit (fail i ω)) ≤
        256*Real.log (Fintype.card I : ℝ)*f b := by
    rw [expect_sum]
    have he (i : I) : (μ.given Y b).expect (fun ω => f (Y ω)*bit (fail i ω)) =
        f b * (μ.given Y b).prob (fun ω => ((μ.given (F i) (F i ω)).map U).tail ell < f b) := by
      rw [μ.given_pullout Y b hb f]
      congr 1
      exact μ.given_prob_congr Y b hb _ _ (by intro ω hω; simp only [fail, hω])
    simp only [he, ← Finset.mul_sum]
    by_cases hf : 0 < f b
    · have h := μ.relative_branch_failures U Y F coarse href ell M m hD hlog hM hm
        hellM hsize hratio b hb (hind b hb) (hatom b hb) hf
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left h hf.le
    · have hz : f b = 0 := le_antisymm (le_of_not_gt hf) (μ.occupancyScalar_nonneg U Y _ b)
      simp [hz]
  have hav := (μ.map Y).expect_mono_on_support _ _ hpoint
  rw [expect_mul] at hav
  have ht := μ.total_conditional_expectation Y (fun ω => ∑ i, f (Y ω)*bit (fail i ω))
  change (μ.map Y).expect (fun b => (μ.given Y b).expect
    (fun ω => ∑ i, f (Y ω)*bit (fail i ω))) = _ at ht
  rw [ht, expect_sum, expect_map] at hav
  exact hav

end FiniteProb
end
end MISLocal
