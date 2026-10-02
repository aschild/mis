import MISLocal.TopLists

/-!
# Dense rectangles force conflict between diffuse output distributions

The proof uses two weighted averaging arguments. It needs no sequential
sampling, no division by a possibly zero tail, and no independence assumption
other than the product of the two output weights in the stated conclusion.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {A B : Type*} [Fintype A] [Fintype B]

/-- If every list of `ell` values has average at least `c`, then weighting the
values by a subprobability distribution costs at most its best `ell` atoms.
The alphabet may be smaller than `ell`; in that case the tail is zero. -/
theorem weighted_tail_lower (P : FiniteProb (Option A)) (v : A → ℝ)
    (hv : ∀ a, 0 ≤ v a) {ell : ℕ} (hell : 0 < ell) {c : ℝ} (hc : 0 ≤ c)
    (hsets : ∀ S : Finset A, S.card = ell → (ell : ℝ) * c ≤ ∑ a ∈ S, v a) :
    P.tail ell * c ≤ ∑ a, P.weight (some a) * v a := by
  let bad : Finset A := Finset.univ.filter (fun a => v a < c)
  have hbad : bad.card < ell := by
    by_contra h
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun a ha =>
      (Finset.mem_filter.mp (hS ha)).2)
    have hs := hsets S hcard
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hlt
    exact not_lt_of_ge hs hlt
  have hgood {a : A} (ha : a ∈ Finset.univ \ bad) : c ≤ v a := by
    have hn := (Finset.mem_sdiff.mp ha).2
    simpa [bad, not_lt] using hn
  calc
    _ ≤ P.listTail bad * c := mul_le_mul_of_nonneg_right (P.tail_minimal ell bad hbad.le) hc
    _ = ∑ a ∈ Finset.univ \ bad, P.weight (some a) * c := by
      simp only [listTail, Finset.sum_mul]
    _ ≤ ∑ a ∈ Finset.univ \ bad, P.weight (some a) * v a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hgood ha) (P.nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun a _ _ => mul_nonneg (P.nonneg _) (hv a))

/-- A matrix with every `ell`-by-`ell` rectangle of density at least `rho`
has weighted density at least `rho` times the product of the two tails. -/
theorem dense_rectangle_tail_product (P : FiniteProb (Option A))
    (Q : FiniteProb (Option B)) (G : A → B → ℝ)
    (hG : ∀ a b, 0 ≤ G a b) {ell : ℕ} (hell : 0 < ell)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hdense : ∀ S : Finset A, S.card = ell → ∀ T : Finset B, T.card = ell →
      rho * (ell : ℝ)^2 ≤ ∑ a ∈ S, ∑ b ∈ T, G a b) :
    rho * P.tail ell * Q.tail ell ≤
      ∑ a, ∑ b, P.weight (some a) * Q.weight (some b) * G a b := by
  have ht := Q.listTail_nonneg (Q.outputList ell)
  change 0 ≤ Q.tail ell at ht
  have h := P.weighted_tail_lower (fun a => ∑ b, Q.weight (some b) * G a b)
    (fun a => Finset.sum_nonneg (fun b _ => mul_nonneg (Q.nonneg _) (hG a b)))
    hell (c := rho * Q.tail ell) (mul_nonneg hrho ht) (by
      intro S hS
      have hinner := Q.weighted_tail_lower (fun b => ∑ a ∈ S, G a b)
        (fun b => Finset.sum_nonneg (fun a _ => hG a b)) hell
        (c := rho * ell) (mul_nonneg hrho (Nat.cast_nonneg _)) (by
          intro T hT
          have hrect := hdense S hS T hT
          rw [Finset.sum_comm] at hrect
          nlinarith)
      simp only [Finset.mul_sum] at hinner
      rw [Finset.sum_comm] at hinner
      nlinarith)
  simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

/-- The form used for Boolean conflict matrices. Zero tails are handled
directly, without cancellation or a hidden positivity premise. -/
theorem dense_boolean_tail_product (P : FiniteProb (Option A))
    (Q : FiniteProb (Option B)) (G : A → B → Prop)
    {ell : ℕ} (hell : 0 < ell)
    (hdense : ∀ S : Finset A, S.card = ell → ∀ T : Finset B, T.card = ell →
      (ell : ℝ)^2 / 4 ≤ ∑ a ∈ S, ∑ b ∈ T, bit (G a b)) :
    P.tail ell * Q.tail ell ≤
      4 * ∑ a, ∑ b, P.weight (some a) * Q.weight (some b) * bit (G a b) := by
  have h := P.dense_rectangle_tail_product Q (fun a b => bit (G a b))
    (fun a b => bit_nonneg _) hell (rho := 1/4) (by norm_num)
    (by intro S hS T hT; convert hdense S hS T hT using 1; ring)
  linarith

end FiniteProb
end
end MISLocal
