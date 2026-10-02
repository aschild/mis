import MISLocal.Conditioning

/-!
# Direct projection onto two smaller views

The reference distribution keeps F and draws the two outputs independently
using their respective smaller-view conditional probabilities. Its relative
entropy is computed exactly. The tree entropy inequality is still an explicit
hypothesis: this module does not replace its missing geometric proof by an axiom.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C Y Z : Type*}
  [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype Y] [Fintype Z]

def projectedPair (μ : FiniteProb Ω) (F : Ω → C) (U : Ω → A) (V : Ω → B)
    (y : C → Y) (z : C → Z) : FiniteProb (C × A × B) where
  weight t := (μ.map F).weight t.1 *
    ((μ.given (fun ω => y (F ω)) (y t.1)).map U).weight t.2.1 *
      ((μ.given (fun ω => z (F ω)) (z t.1)).map V).weight t.2.2
  nonneg t := mul_nonneg (mul_nonneg ((μ.map F).nonneg _)
    (((μ.given _ _).map U).nonneg _)) (((μ.given _ _).map V).nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, FiniteProb.total, mul_one]

theorem dominated_projectedPair (μ : FiniteProb Ω)
    (F : Ω → C) (U : Ω → A) (V : Ω → B) (y : C → Y) (z : C → Z) :
    (μ.map (fun ω => (F ω,U ω,V ω))).Dominated (μ.projectedPair F U V y z) := by
  intro t ht
  have hf : 0 < (μ.map F).weight t.1 :=
    lt_of_lt_of_le ht (μ.prob_mono (fun _ h => congrArg Prod.fst h))
  have huy : 0 < (μ.map (fun ω => (U ω,y (F ω)))).weight (t.2.1,y t.1) :=
    lt_of_lt_of_le ht (μ.prob_mono (fun _ h =>
      congrArg (fun v : C × A × B => (v.2.1,y v.1)) h))
  have hvz : 0 < (μ.map (fun ω => (V ω,z (F ω)))).weight (t.2.2,z t.1) :=
    lt_of_lt_of_le ht (μ.prob_mono (fun _ h =>
      congrArg (fun v : C × A × B => (v.2.2,z v.1)) h))
  have hy := lt_of_lt_of_le huy (μ.pair_weight_le_right U (fun ω => y (F ω)) _ _)
  have hz := lt_of_lt_of_le hvz (μ.pair_weight_le_right V (fun ω => z (F ω)) _ _)
  change 0 < _ * _ * _
  rw [μ.given_pair_mass U _ _ _ hy, μ.given_pair_mass V _ _ _ hz]
  exact mul_pos (mul_pos hf (div_pos huy hy)) (div_pos hvz hz)

theorem kl_projectedPair (μ : FiniteProb Ω)
    (F : Ω → C) (U : Ω → A) (V : Ω → B) (y : C → Y) (z : C → Z) :
    (μ.map (fun ω => (F ω,U ω,V ω))).kl (μ.projectedPair F U V y z) =
      μ.condEntropy U (fun ω => y (F ω)) + μ.condEntropy V (fun ω => z (F ω)) -
        μ.condEntropy (fun ω => (U ω,V ω)) F := by
  change (μ.map (fun ω => (F ω,U ω,V ω))).expect _ = _
  rw [μ.expect_map]
  simp only [condEntropy, μ.entropy_pair_comm (fun ω => (U ω,V ω)) F,
    entropyOf_eq_expect, ← expect_sub, ← expect_add]
  apply μ.expect_congr_on_support
  intro ω hω
  have hf := μ.map_weight_pos F hω
  have hy := μ.map_weight_pos (fun v => y (F v)) hω
  have hz := μ.map_weight_pos (fun v => z (F v)) hω
  have huy := μ.map_weight_pos (fun v => (U v,y (F v))) hω
  have hvz := μ.map_weight_pos (fun v => (V v,z (F v))) hω
  change Real.log _ - Real.log (_ * _ * _) = _
  rw [μ.given_pair_mass U _ _ _ hy, μ.given_pair_mass V _ _ _ hz]
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hf) (ne_of_gt (div_pos huy hy)))
      (ne_of_gt (div_pos hvz hz)),
    Real.log_mul (ne_of_gt hf) (ne_of_gt (div_pos huy hy)),
    Real.log_div (ne_of_gt huy) (ne_of_gt hy),
    Real.log_div (ne_of_gt hvz) (ne_of_gt hz)]
  ring

/-- Arbitrarily many layers may be projected at once. The displayed entropy
inequality is the one missing tree-geometric input, not a definition of a rule. -/
theorem direct_projection_zero_event (μ : FiniteProb Ω)
    (F : Ω → C) (U : Ω → A) (V : Ω → B) (y : C → Y) (z : C → Z)
    (E : C × A × B → Prop) {D K : ℝ} (hD : 0 < D)
    (hsym : μ.condEntropy V (fun ω => z (F ω)) = μ.condEntropy U (fun ω => y (F ω)))
    (htree : (D-1) * μ.condEntropy U (fun ω => y (F ω)) + K ≤
      D/2 * μ.condEntropy (fun ω => (U ω,V ω)) F)
    (hzero : (μ.map (fun ω => (F ω,U ω,V ω))).prob E = 0) :
    (μ.projectedPair F U V y z).prob E ≤
      2 * (μ.condEntropy U (fun ω => y (F ω)) - K) / D := by
  have he := FiniteProb.zero_event_le_kl _ _
    (μ.dominated_projectedPair F U V y z) E hzero
  rw [μ.kl_projectedPair, hsym] at he
  apply (le_div_iff₀ hD).mpr
  have hm := mul_le_mul_of_nonneg_right he hD.le
  nlinarith

/-- The actual projected conflict event is bounded by the rare-output entropy.
Conditional supports, zero conflict, symmetry, and the tree entropy inequality
are each visible premises; no premise states the desired probability bound. -/
theorem direct_projection_rare_bound (μ : FiniteProb Ω)
    (F : Ω → C) (U : Ω → Option A) (V : Ω → Option B) (y : C → Y) (z : C → Z)
    (S : Y → Finset A) (E : C × Option A × Option B → Prop) {D m K : ℝ}
    (hD : 0 < D) (hm : 0 < m) (hK : 0 ≤ K)
    (hcard : ∀ b, ((S b).card : ℝ) ≤ m)
    (hsupport : ∀ b, 0 < (μ.map (fun ω => y (F ω))).weight b → ∀ a, a ∉ S b →
      ((μ.given (fun ω => y (F ω)) b).map U).weight (some a) = 0)
    (hsym : μ.condEntropy V (fun ω => z (F ω)) = μ.condEntropy U (fun ω => y (F ω)))
    (htree : (D-1) * μ.condEntropy U (fun ω => y (F ω)) + K ≤
      D/2 * μ.condEntropy (fun ω => (U ω,V ω)) F)
    (hzero : (μ.map (fun ω => (F ω,U ω,V ω))).prob E = 0) :
    (μ.projectedPair F U V y z).prob E ≤
      2 * massBudget m (μ.prob (fun ω => U ω ≠ none)) / D := by
  have he := μ.direct_projection_zero_event F U V y z E hD hsym htree hzero
  have hs := μ.conditional_rare_entropy_le U (fun ω => y (F ω)) S hm hcard hsupport
  apply he.trans
  apply div_le_div_of_nonneg_right _ hD.le
  linarith

end FiniteProb
end
end MISLocal
