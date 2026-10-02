import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite probability with explicit nonnegative normalized weights

All probability arithmetic is in `ℝ`. An empty sample space cannot carry a
`FiniteProb`: the normalization field rules it out. No division by its cardinality
is used unless a `Nonempty` instance is supplied.
-/

open scoped BigOperators
open scoped Classical

namespace MISLocal

noncomputable section

def bit (p : Prop) : ℝ := if p then 1 else 0

@[simp] theorem bit_true : bit True = 1 := by simp [bit]
@[simp] theorem bit_false : bit False = 0 := by simp [bit]

theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by
  classical
  by_cases h : p <;> simp [bit, h]

theorem bit_le_one (p : Prop) : bit p ≤ 1 := by
  classical
  by_cases h : p <;> simp [bit, h]

theorem bit_mono {p q : Prop} (h : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [bit, hp, h hp]
  · simp only [bit, if_neg hp]
    exact bit_nonneg q

theorem bit_not (p : Prop) : bit (¬p) = 1 - bit p := by
  classical
  by_cases h : p <;> simp [bit, h]

theorem bit_or_le (p q : Prop) : bit (p ∨ q) ≤ bit p + bit q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem bit_and_lower (p q : Prop) : bit p + bit q - 1 ≤ bit (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

structure FiniteProb (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteProb

variable {Ω : Type*} [Fintype Ω] (μ : FiniteProb Ω)

def expect (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

def prob (p : Ω → Prop) : ℝ := μ.expect (fun ω => bit (p ω))

theorem expect_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    μ.expect f = μ.expect g := by
  simp only [expect, h]

@[simp] theorem expect_const (a : ℝ) : μ.expect (fun _ => a) = a := by
  simp [expect, ← Finset.sum_mul, μ.total]

theorem expect_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem expect_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (h ω))

theorem expect_add (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (a : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => a * f ω) = a * μ.expect f := by
  simp [expect, ← Finset.mul_sum, mul_left_comm]

theorem expect_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_le_const {f : Ω → ℝ} {b : ℝ} (h : ∀ ω, f ω ≤ b) :
    μ.expect f ≤ b := by
  simpa using μ.expect_mono h

theorem const_le_expect {f : Ω → ℝ} {b : ℝ} (h : ∀ ω, b ≤ f ω) :
    b ≤ μ.expect f := by
  simpa using μ.expect_mono h

theorem prob_congr {p q : Ω → Prop} (h : ∀ ω, p ω ↔ q ω) :
    μ.prob p = μ.prob q := by
  unfold prob
  exact μ.expect_congr (fun ω => congrArg bit (propext (h ω)))

theorem prob_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) :
    μ.prob p ≤ μ.prob q := μ.expect_mono (fun ω => bit_mono (h ω))

theorem prob_nonneg (p : Ω → Prop) : 0 ≤ μ.prob p :=
  μ.expect_nonneg (fun ω => bit_nonneg (p ω))

theorem prob_le_one (p : Ω → Prop) : μ.prob p ≤ 1 :=
  μ.expect_le_const (fun ω => bit_le_one (p ω))

@[simp] theorem prob_true : μ.prob (fun _ => True) = 1 := by simp [prob]
@[simp] theorem prob_false : μ.prob (fun _ => False) = 0 := by simp [prob]

theorem prob_not (p : Ω → Prop) : μ.prob (fun ω => ¬p ω) = 1 - μ.prob p := by
  simp only [prob, bit_not, expect_sub, expect_const]

theorem prob_or_le (p q : Ω → Prop) :
    μ.prob (fun ω => p ω ∨ q ω) ≤ μ.prob p + μ.prob q := by
  simpa only [prob, expect_add] using μ.expect_mono (fun ω => bit_or_le (p ω) (q ω))

theorem prob_and_lower (p q : Ω → Prop) :
    μ.prob p + μ.prob q - 1 ≤ μ.prob (fun ω => p ω ∧ q ω) := by
  simpa only [prob, expect_sub, expect_add, expect_const] using
    μ.expect_mono (fun ω => bit_and_lower (p ω) (q ω))

theorem prob_exists_le_sum {ι : Type*} [Fintype ι] (p : ι → Ω → Prop) :
    μ.prob (fun ω => ∃ i, p i ω) ≤ ∑ i, μ.prob (p i) := by
  classical
  unfold prob
  rw [← μ.expect_sum Finset.univ (fun i ω => bit (p i ω))]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i, p i ω
  · obtain ⟨i, hi⟩ := h
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => bit (p j ω)) (fun j _ => bit_nonneg (p j ω)) (Finset.mem_univ i)
    simpa only [bit, if_pos hi, if_pos (show ∃ i, p i ω from ⟨i, hi⟩)] using hs
  · simp only [bit, if_neg h]
    exact Finset.sum_nonneg (fun i _ => bit_nonneg (p i ω))

/-- Uniform probability is defined only on a nonempty finite type. -/
def uniform (α : Type*) [Fintype α] [Nonempty α] : FiniteProb α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [h]

theorem uniform_prob_eq_card {α : Type*} [Fintype α] [Nonempty α]
    (p : α → Prop) :
    (uniform α).prob p = (Fintype.card {a // p a} : ℝ) / Fintype.card α := by
  classical
  change (∑ x, (Fintype.card α : ℝ)⁻¹ * bit (p x)) = _
  rw [← Finset.mul_sum]
  simp [bit, Fintype.card_subtype, div_eq_mul_inv, mul_comm]

end FiniteProb
end
end MISLocal
