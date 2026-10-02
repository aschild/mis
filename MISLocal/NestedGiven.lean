import MISLocal.SharedViews
import MISLocal.FirstFailure

/-! Exact successive conditioning, with positivity rather than conventions
about zero-probability fibers doing the cancellation. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem given_positive_original (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) {ω : Ω} (hω : 0 < (μ.given Y b).weight ω) :
    0 < μ.weight ω := by
  rw [μ.given_weight Y b hb] at hω
  have hy := μ.given_support_eq Y b hb
    (show 0 < (μ.given Y b).weight ω by rwa [μ.given_weight Y b hb])
  simp only [hy, bit, if_true, mul_one] at hω
  exact (div_pos_iff_of_pos_right hb).mp hω

theorem given_refinement_mass (μ : FiniteProb Ω) (F : Ω → A) (Y : Ω → B)
    (coarse : A → B) (hY : ∀ ω, Y ω = coarse (F ω)) (a : A)
    (hb : 0 < (μ.map Y).weight (coarse a)) :
    ((μ.given Y (coarse a)).map F).weight a =
      (μ.map F).weight a / (μ.map Y).weight (coarse a) := by
  rw [μ.given_pair_mass F Y a (coarse a) hb]
  congr 1
  apply μ.prob_congr
  intro ω
  simp only [Prod.mk.injEq, hY]
  exact ⟨And.left, fun h => ⟨h,congrArg coarse h⟩⟩

theorem given_given_refinement (μ : FiniteProb Ω) (F : Ω → A) (Y : Ω → B)
    (coarse : A → B) (hY : ∀ ω, Y ω = coarse (F ω)) (a : A)
    (ha : 0 < (μ.map F).weight a) :
    (μ.given Y (coarse a)).given F a = μ.given F a := by
  have hb : 0 < (μ.map Y).weight (coarse a) := lt_of_lt_of_le ha
    (μ.prob_mono (fun ω h => (hY ω).trans (congrArg coarse h)))
  have hm := μ.given_refinement_mass F Y coarse hY a hb
  have hp : 0 < ((μ.given Y (coarse a)).map F).weight a := by rw [hm]; positivity
  ext ω
  rw [given_weight _ F a hp, μ.given_weight Y (coarse a) hb, hm, μ.given_weight F a ha]
  by_cases hf : F ω = a
  · have hy : Y ω = coarse a := (hY ω).trans (congrArg coarse hf)
    simp only [hf, hy, bit, if_true, mul_one]
    field_simp
  · simp [bit, hf]

theorem given_given_at_support (μ : FiniteProb Ω) (F : Ω → A) (Y : Ω → B)
    (coarse : A → B) (hY : ∀ ω, Y ω = coarse (F ω)) (b : B)
    (hb : 0 < (μ.map Y).weight b) {ω : Ω} (hω : 0 < (μ.given Y b).weight ω) :
    (μ.given Y b).given F (F ω) = μ.given F (F ω) := by
  have hy := μ.given_support_eq Y b hb hω
  have ha := μ.map_weight_pos F (μ.given_positive_original Y b hb hω)
  have h := μ.given_given_refinement F Y coarse hY (F ω) ha
  rwa [← hY ω, hy] at h

end FiniteProb
end
end MISLocal
