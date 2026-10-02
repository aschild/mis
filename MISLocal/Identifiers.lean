import MISLocal.FiniteProbability
import Mathlib.Logic.Equiv.Fintype

/-!
# Legal ID completion and tape reindexing

Identifiers use `Fin n`, i.e. 0 through n-1. This is equivalent to paper IDs
1 through n. Completion is a genuine permutation; it does not merely assert
that each locally visible identifier is legal.
-/

open scoped BigOperators
open scoped Classical

namespace MISLocal
noncomputable section

theorem exists_id_completion {n : ℕ} (U : Set (Fin n)) (f : Fin n → Fin n)
    (hinj : Set.InjOn f U) :
    ∃ e : Equiv.Perm (Fin n), ∀ v ∈ U, e v = f v := by
  classical
  let i : U ↪ Fin n := ⟨fun x => f x, fun x y h =>
    Subtype.ext (hinj x.property y.property h)⟩
  let e : U ≃ Set.range i := Equiv.ofInjective i i.injective
  refine ⟨e.extendSubtype, ?_⟩
  intro v hv
  simpa [e, i] using e.extendSubtype_apply_of_mem v hv

/-- The external completion depends only on the tentative ID map and U. -/
def completeIDs {n : ℕ} (U : Set (Fin n)) (f : Fin n → Fin n) :
    Equiv.Perm (Fin n) :=
  if h : Set.InjOn f U then (exists_id_completion U f h).choose else Equiv.refl _

theorem completeIDs_agrees {n : ℕ} (U : Set (Fin n)) (f : Fin n → Fin n)
    (hinj : Set.InjOn f U) (v : Fin n) (hv : v ∈ U) :
    completeIDs U f v = f v := by
  classical
  simp only [completeIDs, dif_pos hinj]
  exact (exists_id_completion U f hinj).choose_spec v hv

theorem completeIDs_bijective {n : ℕ} (U : Set (Fin n)) (f : Fin n → Fin n) :
    Function.Bijective (completeIDs U f) := (completeIDs U f).bijective

/-- Pull an ID-indexed tape table back to vertices. No finiteness of Tape is needed. -/
def reindexTapes {V ID Tape : Type*} (ids : V ≃ ID) : (ID → Tape) ≃ (V → Tape) where
  toFun W v := W (ids v)
  invFun W i := W (ids.symm i)
  left_inv W := by funext i; simp
  right_inv W := by funext v; simp

/-- A permutation of coordinates preserves the exact finite-product weight. -/
theorem tape_product_weight {V ID Tape : Type*} [Fintype V] [Fintype ID]
    (ids : V ≃ ID) (weight : Tape → ℝ) (W : ID → Tape) :
    (∏ v, weight (reindexTapes ids W v)) = ∏ i, weight (W i) := by
  exact ids.prod_comp (fun i => weight (W i))

/-- This is distributional equality for arbitrary finite tape distributions,
not just fair tapes. Since it holds for each bijection, the bijection may depend
on a separately fixed graph. The tape table may not influence that choice. -/
theorem tape_weighted_sum_reindex {V ID Tape : Type*}
    [Fintype V] [Fintype ID] [Fintype Tape]
    (ids : V ≃ ID) (weight : Tape → ℝ) (test : (V → Tape) → ℝ) :
    (∑ W : ID → Tape, (∏ i, weight (W i)) * test (reindexTapes ids W)) =
      ∑ W : V → Tape, (∏ v, weight (W v)) * test W := by
  convert (reindexTapes (Tape := Tape) ids).sum_comp
    (fun W => (∏ v, weight (W v)) * test W) using 1
  apply Finset.sum_congr rfl
  intro W _
  rw [tape_product_weight]

/-- Reduction modulo n has at most two preimages when m ≤ 2n. -/
theorem modulo_fiber_card_le_two {n m : ℕ} (hn : 0 < n) (hm : m ≤ 2 * n)
    (a : Fin n) :
    Fintype.card {x : Fin m // x.val % n = a.val} ≤ 2 := by
  let q : {x : Fin m // x.val % n = a.val} → Fin 2 :=
    fun x => ⟨x.val.val / n, (Nat.div_lt_iff_lt_mul hn).mpr
      (lt_of_lt_of_le x.val.isLt (by simpa [Nat.mul_comm] using hm))⟩
  have hq : Function.Injective q := by
    intro x y h
    have heq : x.val.val / n = y.val.val / n := congrArg Fin.val h
    have hx := Nat.mod_add_div x.val.val n
    have hy := Nat.mod_add_div y.val.val n
    rw [x.property] at hx
    rw [y.property, ← heq] at hy
    apply Subtype.ext
    apply Fin.ext
    omega
  simpa using Fintype.card_le_of_injective q hq

theorem modulo_point_probability {n m : ℕ} (hn : 0 < n)
    (hnm : n ≤ m) (hm : m ≤ 2 * n) (a : Fin n) :
    letI : NeZero m := ⟨by omega⟩
    (FiniteProb.uniform (Fin m)).prob (fun x => x.val % n = a.val) ≤ 2 / (n : ℝ) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  rw [FiniteProb.uniform_prob_eq_card, Fintype.card_fin]
  have hc : (Fintype.card {x : Fin m // x.val % n = a.val} : ℝ) ≤ 2 := by
    exact_mod_cast modulo_fiber_card_le_two hn hm a
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le hn hnm
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hratio := (div_le_div_of_nonneg_right hc hm'.le).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hn' hnm')
  simpa using hratio

end
end MISLocal
