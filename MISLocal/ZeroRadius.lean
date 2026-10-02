import MISLocal.ProjectedBudget
import MISLocal.Extraction

/-!
# Exact zero-radius conflict probability

The two private outputs and the central matrix are sampled independently.
For independent fair matrix entries and identical output distributions this
proves epsilon = p^2/2 on the actual product probability space.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {M A B : Type*} [Fintype M] [Fintype A] [Fintype B]

def product (P : FiniteProb A) (Q : FiniteProb B) : FiniteProb (A × B) where
  weight ab := P.weight ab.1 * Q.weight ab.2
  nonneg ab := mul_nonneg (P.nonneg _) (Q.nonneg _)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, P.total, Q.total]

/-- Independence of the output draws from the matrix is imposed by the
product distribution, not asserted only through one-dimensional marginals. -/
theorem product_conflict_probability (μ : FiniteProb M)
    (P : FiniteProb (Option A)) (Q : FiniteProb (Option B))
    (E : M → A → B → Prop) {c : ℝ}
    (hfair : ∀ a b, μ.prob (fun g => E g a b) = c) :
    (μ.product (P.product Q)).prob (selectedConflict E) =
      P.prob (fun a => a ≠ none) * Q.prob (fun b => b ≠ none) * c := by
  have hswap : (μ.product (P.product Q)).prob (selectedConflict E) =
      P.expect (fun a => Q.expect (fun b => μ.prob (fun g => selectedConflict E (g,a,b)))) := by
    simp only [prob, expect, product, Fintype.sum_prod_type, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [hswap]
  have hnone (b : Option B) : μ.prob (fun g => selectedConflict E (g,none,b)) = 0 := by
    simp [selectedConflict]
  have hnone' (a : A) : μ.prob (fun g => selectedConflict E (g,some a,none)) = 0 := by
    simp [selectedConflict]
  simp only [expect, Fintype.sum_option, hnone, hnone', selectedConflict, hfair,
    prob_false, mul_zero, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ← Finset.sum_mul,
    P.occupied_mass, Q.occupied_mass]
  ring

end FiniteProb

/-- Every individual entry in a uniformly random Boolean matrix is fair. -/
theorem uniform_matrix_entry_fair {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : A) (b : B) :
    (FiniteProb.uniform (A × B → Bool)).prob (fun G => G (a,b) = true) = 1/2 := by
  have h := uniform_first_coordinate (Equiv.funSplitAt (a,b) Bool) true
  simpa using h

/-- A complete zero-radius instance with the actual independent edge matrix. -/
theorem zero_radius_conflict {A : Type*} [Fintype A] [DecidableEq A]
    (P : FiniteProb (Option A)) :
    ((FiniteProb.uniform (A × A → Bool)).product (P.product P)).prob
      (selectedConflict (fun G a b => G (a,b) = true)) =
        (P.prob (fun a => a ≠ none))^2 / 2 := by
  rw [FiniteProb.product_conflict_probability _ P P _ (fun a b => uniform_matrix_entry_fair a b)]
  ring

end
end MISLocal
