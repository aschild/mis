import MISLocal.Conditioning

/-!
# Averaging through smaller views and first-failure mass accounting

These are the finite tower/pullout identities used to relate successive
resamplings to restrictions of the original zero-conflict rule. They are
equalities of conditional averages, not of realized resampled outputs.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem expect_mul_given (μ : FiniteProb Ω) (Z : Ω → A) (g : A → ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => g (Z ω) * (μ.given Z (Z ω)).expect f) =
      μ.expect (fun ω => g (Z ω) * f ω) := by
  rw [← μ.expect_map Z (fun a => g a * (μ.given Z a).expect f)]
  change (∑ a, (μ.map Z).weight a * (g a * (μ.given Z a).expect f)) = _
  calc
    _ = ∑ a, g a * μ.expect (fun ω => bit (Z ω = a) * f ω) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← μ.weighted_given_expect]
      ring
    _ = μ.expect (fun ω => ∑ a, g a * (bit (Z ω = a) * f ω)) := by
      simp only [← μ.expect_mul, ← μ.expect_sum]
    _ = _ := by
      apply μ.expect_congr
      intro ω
      simp [bit]

theorem given_pullout (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) (g : B → ℝ) (f : Ω → ℝ) :
    (μ.given Y b).expect (fun ω => g (Y ω) * f ω) = g b * (μ.given Y b).expect f := by
  apply mul_left_cancel₀ (ne_of_gt hb)
  rw [μ.weighted_given_expect]
  calc
    _ = g b * μ.expect (fun ω => bit (Y ω = b) * f ω) := by
      rw [← μ.expect_mul]
      apply μ.expect_congr
      intro ω
      by_cases h : Y ω = b <;> simp [bit, h, mul_assoc]
    _ = _ := by rw [← μ.weighted_given_expect]; ring

/-- Exact tower identity for nested views. The coarse view is explicitly f ∘ Z. -/
theorem given_tower (μ : FiniteProb Ω) (Z : Ω → A) (coarse : A → B) (b : B)
    (hb : 0 < (μ.map (fun ω => coarse (Z ω))).weight b) (f : Ω → ℝ) :
    (μ.given (fun ω => coarse (Z ω)) b).expect
        (fun ω => (μ.given Z (Z ω)).expect f) =
      (μ.given (fun ω => coarse (Z ω)) b).expect f := by
  apply mul_left_cancel₀ (ne_of_gt hb)
  rw [μ.weighted_given_expect, μ.weighted_given_expect]
  exact μ.expect_mul_given Z (fun a => bit (coarse a = b)) f

/-- One full first-failure induction step: coarse measurable keeping commutes
with averaging an original-rule conditional probability from the larger view. -/
theorem filtered_tower (μ : FiniteProb Ω) (Z : Ω → A) (coarse : A → B) (b : B)
    (hb : 0 < (μ.map (fun ω => coarse (Z ω))).weight b)
    (keep : B → Prop) (f : Ω → ℝ) :
    (μ.given (fun ω => coarse (Z ω)) b).expect
        (fun ω => bit (keep (coarse (Z ω))) * (μ.given Z (Z ω)).expect f) =
      bit (keep b) * (μ.given (fun ω => coarse (Z ω)) b).expect f := by
  rw [μ.given_pullout _ b hb (fun b => bit (keep b)), μ.given_tower Z coarse b hb f]

/-- The occupied mass can be split using ANY finite classification of outputs.
Taking the classification to be first failure or final survival yields exactly
the entropy partition needed by the occupancy proof; no independence is used. -/
theorem classified_mass_sum (μ : FiniteProb Ω) {I : Type*} [Fintype I]
    (occupied : Ω → Prop) (classify : Ω → I) :
    (∑ i, μ.prob (fun ω => occupied ω ∧ classify ω = i)) = μ.prob occupied := by
  unfold prob
  rw [← μ.expect_sum]
  apply μ.expect_congr
  intro ω
  by_cases h : occupied ω <;> simp [bit, h]

end FiniteProb
end
end MISLocal
