import MISLocal.TableSampling
import MISLocal.ScalarEntropy

/-! Independent private Bernoulli rounding of a local number in [0,1].
The two-point moment is the original expectation of the product, exactly. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteProb Bool where
  weight b := if b then p else 1-p
  nonneg b := by cases b <;> simp_all
  total := by simp [Fintype.sum_bool]

@[simp] theorem bernoulli_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulli p hp0 hp1).prob (fun b => b = true) = p := by
  simp [prob, expect, bernoulli, Fintype.sum_bool, bit]

variable {Ω I B : Type*} [Fintype Ω] [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]

theorem bernoulli_table_mean (μ : FiniteProb Ω) (Y : I → Ω → B) (f : I → B → ℝ)
    (hf0 : ∀ i b, 0 ≤ f i b) (hf1 : ∀ i b, f i b ≤ 1) (i : I) :
    (μ.product (tableProbability (fun i b => bernoulli (f i b) (hf0 i b) (hf1 i b)))).prob
      (fun x => tableDraw Y i x = true) = μ.expect (fun ω => f i (Y i ω)) := by
  rw [prob, product_expect]
  apply μ.expect_congr
  intro ω
  exact (table_expect_one _ i (Y i ω) (fun b => bit (b=true))).trans (bernoulli_true _ _ _)

theorem bernoulli_table_moment (μ : FiniteProb Ω) (Y : I → Ω → B) (f : I → B → ℝ)
    (hf0 : ∀ i b, 0 ≤ f i b) (hf1 : ∀ i b, f i b ≤ 1) (i j : I) (hji : j ≠ i) :
    (μ.product (tableProbability (fun i b => bernoulli (f i b) (hf0 i b) (hf1 i b)))).prob
      (fun x => tableDraw Y i x = true ∧ tableDraw Y j x = true) =
        μ.expect (fun ω => f i (Y i ω)*f j (Y j ω)) := by
  rw [prob, product_expect]
  apply μ.expect_congr
  intro ω
  have he (t : I → B → Bool) :
      bit (tableDraw Y i (ω,t) = true ∧ tableDraw Y j (ω,t) = true) =
        bit (t i (Y i ω) = true)*bit (t j (Y j ω) = true) := by
    by_cases hi : t i (Y i ω) = true <;> by_cases hj : t j (Y j ω) = true <;>
      simp [tableDraw, bit, hi, hj]
  rw [expect_congr _ he, table_expect_pair _ i j hji (Y i ω) (Y j ω)
    (fun b => bit (b=true)) (fun b => bit (b=true))]
  change (bernoulli _ _ _).prob _ * (bernoulli _ _ _).prob _ = _
  rw [bernoulli_true, bernoulli_true]

/-- The scalar estimate follows from the Shannon inequality for the
constructed private-table experiment. The Shannon premise is discharged by
source charging when the views and the field have the required geometry. -/
theorem scalar_moment_from_rounding (μ : FiniteProb Ω) (Y : I → Ω → B) (f : I → B → ℝ)
    (hf0 : ∀ i b, 0 ≤ f i b) (hf1 : ∀ i b, f i b ≤ 1) (i j : I) (hji : j ≠ i)
    {D p : ℝ} (hD : 0 < D)
    (hi : μ.expect (fun ω => f i (Y i ω)) = p) (hj : μ.expect (fun ω => f j (Y j ω)) = p)
    (htree : let ν := μ.product (tableProbability (fun i b => bernoulli (f i b) (hf0 i b) (hf1 i b)))
      (D/2)*ν.entropyOf (fun x => (tableDraw Y i x,tableDraw Y j x)) ≥
        (D-1)*ν.entropyOf (tableDraw Y i)) :
    p^2/2-2*binaryEntropy p/D ≤ μ.expect (fun ω => f i (Y i ω)*f j (Y j ω)) := by
  have h := scalar_pair_overlap
    (μ.product (tableProbability (fun i b => bernoulli (f i b) (hf0 i b) (hf1 i b))))
    (tableDraw Y i) (tableDraw Y j) hD
    ((bernoulli_table_mean μ Y f hf0 hf1 i).trans hi)
    ((bernoulli_table_mean μ Y f hf0 hf1 j).trans hj) htree
  rwa [bernoulli_table_moment μ Y f hf0 hf1 i j hji] at h

end FiniteProb
end
end MISLocal
