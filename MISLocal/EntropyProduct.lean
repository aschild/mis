import MISLocal.IndependentEvents
import MISLocal.Hellinger

/-! Product entropies and information revealed by one additional variable. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C T : Type*}
  [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype T]

@[ext] theorem ext {P Q : FiniteProb Ω} (h : ∀ ω, P.weight ω = Q.weight ω) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

@[simp] theorem map_id (μ : FiniteProb Ω) : μ.map id = μ := by
  ext ω
  simp [map, prob, expect, bit]

theorem map_comp (μ : FiniteProb Ω) (X : Ω → A) (f : A → B) :
    (μ.map X).map f = μ.map (fun ω => f (X ω)) := by
  ext b
  exact μ.prob_map X _

theorem entropyOf_same_fibers (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B)
    (h : ∀ ω ω', X ω = X ω' ↔ Y ω = Y ω') : μ.entropyOf X = μ.entropyOf Y := by
  rw [entropyOf_eq_expect, entropyOf_eq_expect]
  apply μ.expect_congr
  intro ω
  exact congrArg (fun p : ℝ => -Real.log p) (μ.prob_congr (fun ω' => h ω' ω))

theorem entropyOf_determined_le (μ : FiniteProb Ω) (Y : Ω → B) (f : B → A) :
    μ.entropyOf (fun ω => f (Y ω)) ≤ μ.entropyOf Y := by
  have h := μ.condEntropy_nonneg Y (fun ω => f (Y ω))
  rw [condEntropy, μ.entropy_pair_comm, μ.entropy_deterministic_pair] at h
  linarith

theorem product_expect (P : FiniteProb A) (Q : FiniteProb B) (f : A × B → ℝ) :
    (P.product Q).expect f = P.expect (fun a => Q.expect (fun b => f (a,b))) := by
  simp only [expect, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem product_map_fst (P : FiniteProb A) (Q : FiniteProb B) :
    (P.product Q).map Prod.fst = P := by
  ext a
  change (P.product Q).expect (fun ab => bit (ab.1 = a)) = _
  rw [product_expect]
  simp only [expect_const]
  simp [expect, bit]

theorem product_map_snd (P : FiniteProb A) (Q : FiniteProb B) :
    (P.product Q).map Prod.snd = Q := by
  ext b
  change (P.product Q).expect (fun ab => bit (ab.2 = b)) = _
  rw [product_expect]
  change P.expect (fun _ => Q.expect (fun b' => bit (b' = b))) = Q.weight b
  have h : Q.expect (fun b' => bit (b' = b)) = Q.weight b := by simp [expect, bit]
  rw [h, expect_const]

theorem dominated_marginalProduct (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    (μ.map (fun ω => (X ω,Y ω))).Dominated ((μ.map X).product (μ.map Y)) := by
  intro ab hab
  have hx := lt_of_lt_of_le hab (μ.prob_mono (fun _ h => congrArg Prod.fst h))
  have hy := lt_of_lt_of_le hab (μ.prob_mono (fun _ h => congrArg Prod.snd h))
  exact mul_pos hx hy

theorem kl_marginalProduct (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    (μ.map (fun ω => (X ω,Y ω))).kl ((μ.map X).product (μ.map Y)) =
      μ.entropyOf X + μ.entropyOf Y - μ.entropyOf (fun ω => (X ω,Y ω)) := by
  change (μ.map (fun ω => (X ω,Y ω))).expect _ = _
  rw [μ.expect_map]
  simp only [entropyOf_eq_expect, ← μ.expect_add, ← μ.expect_sub]
  apply μ.expect_congr_on_support
  intro ω hω
  have hx := ne_of_gt (μ.map_weight_pos X hω)
  have hy := ne_of_gt (μ.map_weight_pos Y hω)
  change Real.log _ - Real.log (_ * _) = _
  rw [Real.log_mul hx hy]
  ring

theorem product_entropy (P : FiniteProb A) (Q : FiniteProb B) :
    (P.product Q).entropy = P.entropy + Q.entropy := by
  have h := (P.product Q).kl_marginalProduct Prod.fst Prod.snd
  have hid : (fun ab : A × B => (ab.1,ab.2)) = id := rfl
  rw [hid, map_id, product_map_fst, product_map_snd] at h
  simp only [kl, sub_self, mul_zero, Finset.sum_const_zero, entropyOf,
    product_map_fst, product_map_snd, map_id] at h
  linarith

/-- Mutual information is the entropy drop caused by revealing `X` after
the previously revealed data `T`. This identity requires no independence. -/
theorem reveal_gain_symm (μ : FiniteProb Ω) (Y : Ω → A) (X : Ω → B) (Z : Ω → T) :
    μ.condEntropy Y Z - μ.condEntropy Y (fun ω => (Z ω,X ω)) =
      μ.condEntropy X Z - μ.condEntropy X (fun ω => (Z ω,Y ω)) := by
  have h1 := μ.entropy_pair_comm Z X
  have h2 := μ.entropy_pair_comm Z Y
  have h3 := μ.entropyOf_same_fibers (fun ω => (Y ω,Z ω,X ω))
    (fun ω => (X ω,Z ω,Y ω)) (by intro ω ω'; simp only [Prod.mk.injEq]; tauto)
  simp only [condEntropy]
  linarith

theorem reveal_gain_nonneg (μ : FiniteProb Ω) (Y : Ω → A) (X : Ω → B) (Z : Ω → T) :
    0 ≤ μ.condEntropy Y Z - μ.condEntropy Y (fun ω => (Z ω,X ω)) :=
  sub_nonneg.mpr (μ.conditioning_reduces Y Z X)

/-- A joint endpoint state gains at least as much information as either
component when a raw input is revealed. -/
theorem reveal_gain_pair (μ : FiniteProb Ω) (Y : Ω → A) (W : Ω → C)
    (X : Ω → B) (Z : Ω → T) :
    μ.condEntropy Y Z - μ.condEntropy Y (fun ω => (Z ω,X ω)) ≤
      μ.condEntropy (fun ω => (Y ω,W ω)) Z -
        μ.condEntropy (fun ω => (Y ω,W ω)) (fun ω => (Z ω,X ω)) := by
  rw [μ.reveal_gain_symm Y X Z, μ.reveal_gain_symm (fun ω => (Y ω,W ω)) X Z]
  have h := μ.conditioning_reduces X (fun ω => (Z ω,Y ω)) W
  have he := μ.entropyOf_same_fibers (fun ω => (X ω,((Z ω,Y ω),W ω)))
    (fun ω => (X ω,(Z ω,(Y ω,W ω)))) (by intro ω ω'; simp only [Prod.mk.injEq]; tauto)
  have he' := μ.entropy_pair_assoc Z Y W
  simp only [condEntropy] at h ⊢
  linarith

end FiniteProb
end
end MISLocal
