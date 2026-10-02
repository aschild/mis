import MISLocal.Entropy

/-!
# Conditional entropy for finite random variables

Conditional entropy is joint entropy minus the conditioning entropy. The
submodular inequality and "conditioning reduces entropy" are derived from
Gibbs' inequality for the actual finite distributions, not assumed.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

theorem expect_congr_on_support (μ : FiniteProb Ω) (f g : Ω → ℝ)
    (h : ∀ ω, 0 < μ.weight ω → f ω = g ω) : μ.expect f = μ.expect g := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hz : μ.weight ω = 0
  · simp [hz]
  · rw [h ω (lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hz))]

theorem expect_mono_on_support (μ : FiniteProb Ω) (f g : Ω → ℝ)
    (h : ∀ ω, 0 < μ.weight ω → f ω ≤ g ω) : μ.expect f ≤ μ.expect g := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hz : μ.weight ω = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left
      (h ω (lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hz))) (μ.nonneg ω)

theorem entropyOf_comp_injective (μ : FiniteProb Ω) (X : Ω → A)
    (f : A → B) (hf : Function.Injective f) :
    μ.entropyOf (fun ω => f (X ω)) = μ.entropyOf X := by
  rw [entropyOf_eq_expect, entropyOf_eq_expect]
  apply μ.expect_congr
  intro ω
  apply congrArg (fun t : ℝ => -Real.log t)
  exact μ.prob_congr (fun v => hf.eq_iff)

theorem entropy_pair_comm (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    μ.entropyOf (fun ω => (X ω, Y ω)) = μ.entropyOf (fun ω => (Y ω, X ω)) := by
  exact (μ.entropyOf_comp_injective (fun ω => (X ω, Y ω))
    (Equiv.prodComm A B) (Equiv.prodComm A B).injective).symm

theorem entropy_pair_assoc (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    μ.entropyOf (fun ω => ((X ω, Y ω), Z ω)) =
      μ.entropyOf (fun ω => (X ω, Y ω, Z ω)) := by
  exact (μ.entropyOf_comp_injective (fun ω => ((X ω, Y ω), Z ω))
    (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C).injective).symm

theorem entropy_deterministic_pair (μ : FiniteProb Ω) (Y : Ω → B) (f : B → A) :
    μ.entropyOf (fun ω => (f (Y ω), Y ω)) = μ.entropyOf Y := by
  apply μ.entropyOf_comp_injective Y (fun b => (f b, b))
  intro b c h
  exact congrArg Prod.snd h

theorem condEntropy_deterministic (μ : FiniteProb Ω) (Y : Ω → B) (f : B → A) :
    μ.condEntropy (fun ω => f (Y ω)) Y = 0 := by
  simp [condEntropy, entropy_deterministic_pair]

theorem pair_weight_le_right (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B)
    (a : A) (b : B) : (μ.map (fun ω => (X ω, Y ω))).weight (a,b) ≤
      (μ.map Y).weight b := by
  exact μ.prob_mono (fun _ h => congrArg Prod.snd h)

theorem pair_sum_left (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (b : B) :
    (∑ a, (μ.map (fun ω => (X ω, Y ω))).weight (a,b)) = (μ.map Y).weight b := by
  simp only [map, prob, expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : Y ω = b <;> simp [bit, Prod.ext_iff, h]

theorem pair_sum_right (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (a : A) :
    (∑ b, (μ.map (fun ω => (X ω, Y ω))).weight (a,b)) = (μ.map X).weight a := by
  simp only [map, prob, expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : X ω = a <;> simp [bit, Prod.ext_iff, h]

theorem condEntropy_nonneg (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    0 ≤ μ.condEntropy X Y := by
  unfold condEntropy
  apply sub_nonneg.mpr
  rw [entropyOf_eq_expect, entropyOf_eq_expect]
  apply μ.expect_mono_on_support
  intro ω hω
  exact neg_le_neg (Real.log_le_log (μ.map_weight_pos (fun v => (X v, Y v)) hω)
    (μ.pair_weight_le_right X Y (X ω) (Y ω)))

/-- Conditional product distribution: X and Z are independent given Y.
Zero-probability Y fibers contribute exactly zero. -/
def conditionalProduct (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    FiniteProb (A × B × C) where
  weight abc := (μ.map (fun ω => (X ω, Y ω))).weight (abc.1, abc.2.1) *
    (μ.map (fun ω => (Y ω, Z ω))).weight (abc.2.1, abc.2.2) /
      (μ.map Y).weight abc.2.1
  nonneg abc := div_nonneg (mul_nonneg (μ.prob_nonneg _) (μ.prob_nonneg _))
    (μ.prob_nonneg _)
  total := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc
      _ = ∑ b, (μ.map Y).weight b := by
        apply Finset.sum_congr rfl
        intro b _
        simp only [← Finset.sum_div, ← Finset.mul_sum, μ.pair_sum_right Y Z,
          ← Finset.sum_mul, μ.pair_sum_left X Y]
        by_cases hb : (μ.map Y).weight b = 0
        · simp [hb]
        · exact mul_div_cancel_right₀ _ hb
      _ = 1 := (μ.map Y).total

theorem dominated_conditionalProduct (μ : FiniteProb Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    (μ.map (fun ω => (X ω, Y ω, Z ω))).Dominated (μ.conditionalProduct X Y Z) := by
  intro abc h
  have hxy : 0 < (μ.map (fun ω => (X ω, Y ω))).weight (abc.1,abc.2.1) :=
    lt_of_lt_of_le h (μ.prob_mono (fun _ he =>
      congrArg (fun p : A × B × C => (p.1,p.2.1)) he))
  have hyz : 0 < (μ.map (fun ω => (Y ω, Z ω))).weight abc.2 :=
    lt_of_lt_of_le h (μ.prob_mono (fun _ he => congrArg Prod.snd he))
  have hy : 0 < (μ.map Y).weight abc.2.1 :=
    lt_of_lt_of_le hxy (μ.pair_weight_le_right X Y abc.1 abc.2.1)
  exact div_pos (mul_pos hxy hyz) hy

/-- An exact entropy identity for the relative entropy of the conditional product. -/
theorem kl_conditionalProduct (μ : FiniteProb Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    (μ.map (fun ω => (X ω, Y ω, Z ω))).kl (μ.conditionalProduct X Y Z) =
      μ.entropyOf (fun ω => (X ω,Y ω)) + μ.entropyOf (fun ω => (Y ω,Z ω)) -
        μ.entropyOf Y - μ.entropyOf (fun ω => (X ω,Y ω,Z ω)) := by
  change (μ.map (fun ω => (X ω, Y ω, Z ω))).expect _ = _
  rw [μ.expect_map]
  simp only [entropyOf_eq_expect, ← expect_add, ← expect_sub]
  apply μ.expect_congr_on_support
  intro ω hω
  have hxy := ne_of_gt (μ.map_weight_pos (fun v => (X v,Y v)) hω)
  have hyz := ne_of_gt (μ.map_weight_pos (fun v => (Y v,Z v)) hω)
  have hy := ne_of_gt (μ.map_weight_pos Y hω)
  change Real.log _ - Real.log (_ * _ / _) = _
  rw [Real.log_div (mul_ne_zero hxy hyz) hy, Real.log_mul hxy hyz]
  ring

theorem entropy_submodular (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    μ.entropyOf Y + μ.entropyOf (fun ω => (X ω,Y ω,Z ω)) ≤
      μ.entropyOf (fun ω => (X ω,Y ω)) + μ.entropyOf (fun ω => (Y ω,Z ω)) := by
  have h := FiniteProb.kl_nonneg _ _ (μ.dominated_conditionalProduct X Y Z)
  rw [μ.kl_conditionalProduct] at h
  linarith

theorem conditioning_reduces (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    μ.condEntropy X (fun ω => (Y ω,Z ω)) ≤ μ.condEntropy X Y := by
  have h := μ.entropy_submodular X Y Z
  simp only [condEntropy]
  linarith

/-- The conditional chain rule is an identity, with no independence assumption. -/
theorem condEntropy_chain (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    μ.condEntropy (fun ω => (X ω,Y ω)) Z =
      μ.condEntropy Y Z + μ.condEntropy X (fun ω => (Y ω,Z ω)) := by
  simp only [condEntropy, μ.entropy_pair_assoc]
  ring

end FiniteProb
end
end MISLocal
