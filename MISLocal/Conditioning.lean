import MISLocal.ConditionalEntropy
import MISLocal.RareEntropy

/-!
# Finite conditional probabilities, including null fibers

On a null conditioning fiber `given` returns the original distribution.
Its value on such fibers is irrelevant because every identity multiplies it
by the fiber probability. Positivity is explicit whenever a quotient is used.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

def given (μ : FiniteProb Ω) (Y : Ω → B) (b : B) : FiniteProb Ω :=
  if hb : 0 < (μ.map Y).weight b then
    { weight := fun ω => μ.weight ω * bit (Y ω = b) / (μ.map Y).weight b
      nonneg := fun ω => div_nonneg (mul_nonneg (μ.nonneg ω) (bit_nonneg _)) hb.le
      total := by
        rw [← Finset.sum_div]
        change (μ.map Y).weight b / (μ.map Y).weight b = 1
        exact div_self (ne_of_gt hb) }
  else μ

theorem given_weight (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) (ω : Ω) :
    (μ.given Y b).weight ω = μ.weight ω * bit (Y ω = b) / (μ.map Y).weight b := by
  simp [given, hb]

theorem weighted_given_expect (μ : FiniteProb Ω) (Y : Ω → B) (b : B) (f : Ω → ℝ) :
    (μ.map Y).weight b * (μ.given Y b).expect f =
      μ.expect (fun ω => bit (Y ω = b) * f ω) := by
  by_cases hb : 0 < (μ.map Y).weight b
  · simp only [expect, given_weight μ Y b hb, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    field_simp
    ring
  · have hb0 : (μ.map Y).weight b = 0 :=
      le_antisymm (le_of_not_gt hb) ((μ.map Y).nonneg b)
    rw [hb0, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hω : Y ω = b
    · have hz := μ.weight_eq_zero_of_prob_zero (fun ω => Y ω = b) hb0 hω
      simp [hz]
    · simp [bit, hω]

theorem total_conditional_expectation (μ : FiniteProb Ω) (Y : Ω → B) (f : Ω → ℝ) :
    (∑ b, (μ.map Y).weight b * (μ.given Y b).expect f) = μ.expect f := by
  simp only [μ.weighted_given_expect]
  rw [← μ.expect_sum]
  apply μ.expect_congr
  intro ω
  simp [bit]

theorem given_pair_mass (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (a : A) (b : B)
    (hb : 0 < (μ.map Y).weight b) :
    ((μ.given Y b).map X).weight a =
      (μ.map (fun ω => (X ω,Y ω))).weight (a,b) / (μ.map Y).weight b := by
  change (∑ ω, (μ.given Y b).weight ω * bit (X ω = a)) = _
  simp only [μ.given_weight Y b hb]
  change _ = (∑ ω, μ.weight ω * bit ((X ω,Y ω) = (a,b))) / _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hx : X ω = a <;> by_cases hy : Y ω = b <;>
    simp [bit, Prod.ext_iff, hx, hy]

/-- Conditional entropy equals the average entropy on conditioning fibers. -/
theorem condEntropy_eq_average (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    μ.condEntropy X Y =
      ∑ b, (μ.map Y).weight b * (μ.given Y b).entropyOf X := by
  simp only [entropyOf_eq_expect, μ.weighted_given_expect]
  rw [← μ.expect_sum]
  simp only [condEntropy, entropyOf_eq_expect, ← μ.expect_sub]
  apply μ.expect_congr_on_support
  intro ω hω
  simp only [bit, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hy := μ.map_weight_pos Y hω
  have hxy := μ.map_weight_pos (fun v => (X v,Y v)) hω
  rw [μ.given_pair_mass X Y (X ω) (Y ω) hy,
    Real.log_div (ne_of_gt hxy) (ne_of_gt hy)]
  ring

/-- Jensen's inequality for the continuous rare-output entropy budget. -/
theorem expect_massBudget_le (μ : FiniteProb Ω) (x : Ω → ℝ)
    (hx : ∀ ω, 0 ≤ x ω) (m : ℝ) :
    μ.expect (fun ω => massBudget m (x ω)) ≤ massBudget m (μ.expect x) := by
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := μ.weight) (p := x)
    (fun ω _ => μ.nonneg ω) μ.total (fun ω _ => hx ω)
  simp only [smul_eq_mul] at hj
  simp only [massBudget, expect, mul_add, Finset.sum_add_distrib,
    ← mul_assoc, ← Finset.sum_mul]
  linarith

/-- The support list may depend on the smaller view. Its entropy cost still
depends only on the AVERAGE nonempty-output probability. Null fibers are harmless. -/
theorem conditional_rare_entropy_le (μ : FiniteProb Ω) (X : Ω → Option A)
    (Y : Ω → B) (S : B → Finset A) {m : ℝ} (hm : 0 < m)
    (hcard : ∀ b, ((S b).card : ℝ) ≤ m)
    (hsupport : ∀ b, 0 < (μ.map Y).weight b → ∀ a, a ∉ S b →
      ((μ.given Y b).map X).weight (some a) = 0) :
    μ.condEntropy X Y ≤ massBudget m (μ.prob (fun ω => X ω ≠ none)) := by
  rw [μ.condEntropy_eq_average X Y]
  have hpoint (b : B) : (μ.map Y).weight b * (μ.given Y b).entropyOf X ≤
      (μ.map Y).weight b * massBudget m ((μ.given Y b).prob (fun ω => X ω ≠ none)) := by
    by_cases hb : 0 < (μ.map Y).weight b
    · have h := ((μ.given Y b).map X).rare_entropy_le (S b) hm (hcard b) (hsupport b hb)
      rw [(μ.given Y b).prob_map] at h
      exact mul_le_mul_of_nonneg_left h hb.le
    · have hb0 := le_antisymm (le_of_not_gt hb) ((μ.map Y).nonneg b)
      simp [hb0]
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  have hj := (μ.map Y).expect_massBudget_le
    (fun b => (μ.given Y b).prob (fun ω => X ω ≠ none))
    (fun b => (μ.given Y b).prob_nonneg _) m
  have ht := μ.total_conditional_expectation Y (fun ω => bit (X ω ≠ none))
  change (μ.map Y).expect (fun b => (μ.given Y b).prob (fun ω => X ω ≠ none)) = _ at ht
  rw [ht] at hj
  exact hs.trans hj

end FiniteProb
end
end MISLocal
