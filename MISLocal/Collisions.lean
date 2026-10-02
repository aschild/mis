import MISLocal.FiniteProbability
import Mathlib.Data.Finset.Prod

/-!
# Collision probabilities, including the factor of two

The ordered-pair proof counts both (i,j) and (j,i) whenever a collision occurs.
The resulting bound is L(L-1)/n, not 2L(L-1)/n. The natural subtraction in the
off-diagonal cardinality is cast only after proving the requisite inequality.
The statement itself uses real subtraction and also covers L = 0 and L = 1.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

variable {Ω : Type*} [Fintype Ω] (μ : FiniteProb Ω)

theorem collision_probability_le {ID : Type*} [Fintype ID]
    (X Y : Ω → ID) (c : ℝ)
    (hind : ∀ a b, μ.prob (fun ω => X ω = a ∧ Y ω = b) =
      μ.prob (fun ω => X ω = a) * μ.prob (fun ω => Y ω = b))
    (hpoint : ∀ a, μ.prob (fun ω => X ω = a) ≤ c) :
    μ.prob (fun ω => X ω = Y ω) ≤ c := by
  have heq : μ.prob (fun ω => X ω = Y ω) =
      ∑ a, μ.prob (fun ω => X ω = a ∧ Y ω = a) := by
    unfold FiniteProb.prob
    rw [← μ.expect_sum]
    apply μ.expect_congr
    intro ω
    by_cases h : X ω = Y ω
    · simp [bit, h]
    · have hh (a : ID) : ¬(X ω = a ∧ Y ω = a) := by
        rintro ⟨hx, hy⟩
        exact h (hx.trans hy.symm)
      simp [bit, h, hh]
  have hsum : (∑ a, μ.prob (fun ω => Y ω = a)) = 1 := by
    unfold FiniteProb.prob
    rw [← μ.expect_sum]
    simp [bit]
  rw [heq]
  calc
    _ = ∑ a, μ.prob (fun ω => X ω = a) * μ.prob (fun ω => Y ω = a) := by
      simp only [hind]
    _ ≤ ∑ a, c * μ.prob (fun ω => Y ω = a) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (hpoint a) (μ.prob_nonneg _)
    _ = c := by rw [← Finset.mul_sum, hsum, mul_one]

/-- A union bound requiring only pairwise collision bounds, not full independence. -/
theorem local_collision_bound {I ID : Type*} [Fintype I]
    (X : I → Ω → ID) (n : ℕ) (hn : 0 < n)
    (hpair : ∀ i j, i ≠ j → μ.prob (fun ω => X i ω = X j ω) ≤ 2 / (n : ℝ)) :
    μ.prob (fun ω => ¬Function.Injective (fun i => X i ω)) ≤
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) / (n : ℝ) := by
  let pairs : Finset (I × I) := Finset.univ.offDiag
  have hpoint (ω : Ω) :
      2 * bit (¬Function.Injective (fun i => X i ω)) ≤
        ∑ p ∈ pairs, bit (X p.1 ω = X p.2 ω) := by
    by_cases hinj : Function.Injective (fun i => X i ω)
    · simp only [bit, not_true_eq_false, hinj, if_false, mul_zero]
      exact Finset.sum_nonneg (fun p _ => bit_nonneg _)
    · obtain ⟨i, j, heq, hne⟩ : ∃ i j, X i ω = X j ω ∧ i ≠ j := by
        unfold Function.Injective at hinj
        push_neg at hinj
        exact hinj
      have hp : (i, j) ≠ (j, i) := by
        intro h
        exact hne (congrArg Prod.fst h)
      have hsub : ({(i, j), (j, i)} : Finset (I × I)) ⊆ pairs := by
        intro p hp'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
        rcases hp' with rfl | rfl <;> simp [pairs, hne, hne.symm]
      have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => bit_nonneg (X p.1 ω = X p.2 ω))
      have hsmall : (∑ p ∈ ({(i, j), (j, i)} : Finset (I × I)),
          bit (X p.1 ω = X p.2 ω)) = 2 := by
        rw [Finset.sum_pair hp]
        simp only [Prod.fst, Prod.snd, bit, if_pos heq, if_pos heq.symm]
        norm_num
      rw [hsmall] at hs
      simpa only [bit, if_pos hinj, mul_one] using hs
  have hmean := μ.expect_mono hpoint
  rw [μ.expect_mul, μ.expect_sum] at hmean
  have hsum : (∑ p ∈ pairs, μ.prob (fun ω => X p.1 ω = X p.2 ω)) ≤
      (pairs.card : ℝ) * (2 / (n : ℝ)) := by
    calc
      _ ≤ ∑ _p ∈ pairs, 2 / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpair p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
      _ = _ := by simp
  have hcast : (pairs.card : ℝ) =
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) := by
    have hle : Fintype.card I ≤ Fintype.card I * Fintype.card I := Nat.le_mul_self _
    simp only [pairs, Finset.offDiag_card, Finset.card_univ, Nat.cast_sub hle,
      Nat.cast_mul]
    ring
  rw [hcast] at hsum
  change 2 * μ.prob (fun ω => ¬Function.Injective (fun i => X i ω)) ≤ _ at hmean
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := hmean.trans hsum
  rw [← mul_div_assoc] at h
  have hh := (le_div_iff₀ hn').mp h
  apply (le_div_iff₀ hn').mpr
  nlinarith

/-- Apply the pairwise-independent ID hypothesis and the maximum point mass. -/
theorem local_collision_bound_of_pairwise_independent {I ID : Type*}
    [Fintype I] [Fintype ID] (X : I → Ω → ID) (n : ℕ) (hn : 0 < n)
    (hind : ∀ i j, i ≠ j → ∀ a b,
      μ.prob (fun ω => X i ω = a ∧ X j ω = b) =
        μ.prob (fun ω => X i ω = a) * μ.prob (fun ω => X j ω = b))
    (hpoint : ∀ i a, μ.prob (fun ω => X i ω = a) ≤ 2 / (n : ℝ)) :
    μ.prob (fun ω => ¬Function.Injective (fun i => X i ω)) ≤
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) / (n : ℝ) := by
  apply local_collision_bound μ X n hn
  intro i j hij
  exact collision_probability_le μ (X i) (X j) (2 / (n : ℝ))
    (hind i j hij) (hpoint i)

end
end MISLocal
