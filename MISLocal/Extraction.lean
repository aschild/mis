import MISLocal.FiniteProbability
import Mathlib.Logic.Equiv.Prod

/-!
# The algebra behind directed-block XOR extraction

The source is an array of independent uniform outgoing strings, with one
coordinate per vertex and incident edge. Summing over incident edges gives a
jointly uniform array of vertex strings. Specialize the finite additive group
to `Fin q → ZMod 2` for q-bit strings and bitwise XOR.

The proof chooses a distinguished incident edge only to count fibers. The
extractor itself is the sum over ALL incident edges and is permutation invariant.
This module does not construct skeleton edge-matrix coordinates or prove their
identification with this product sample space.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

/-- The opposite off-diagonal blocks of an edge matrix are disjoint. -/
theorem directed_blocks_disjoint {K : Type*} (P : Set K) :
    Disjoint (P ×ˢ Pᶜ) (Pᶜ ×ˢ P) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hy.1 hx.1

def sumSplit {I A : Type*} [Fintype I] [AddCommGroup A] (j : I) :
    (I → A) ≃ A × ({i : I // i ≠ j} → A) :=
  (Equiv.funSplitAt j A).trans
    { toFun := fun x => (x.1 + ∑ i, x.2 i, x.2)
      invFun := fun x => (x.1 - ∑ i, x.2 i, x.2)
      left_inv := by intro x; ext <;> simp
      right_inv := by intro x; ext <;> simp }

theorem sumSplit_first {I A : Type*} [Fintype I] [AddCommGroup A]
    (j : I) (x : I → A) : (sumSplit j x).1 = ∑ i, x i := by
  exact (Fintype.sum_eq_add_sum_subtype_ne x j).symm

/-- A bijection between all source arrays and (all vertex sums, unused freedom). -/
def jointSumSplit {V I A : Type*} [Fintype I] [AddCommGroup A] (j : I) :
    (V → I → A) ≃ (V → A) × (V → {i : I // i ≠ j} → A) where
  toFun x := (fun v => (sumSplit j (x v)).1, fun v => (sumSplit j (x v)).2)
  invFun x v := (sumSplit j).symm (x.1 v, x.2 v)
  left_inv x := by
    funext v
    exact (sumSplit j).symm_apply_apply (x v)
  right_inv x := by
    apply Prod.ext <;> funext v
    · exact congrArg Prod.fst ((sumSplit j).apply_symm_apply (x.1 v, x.2 v))
    · exact congrArg Prod.snd ((sumSplit j).apply_symm_apply (x.1 v, x.2 v))

theorem jointSumSplit_first {V I A : Type*} [Fintype I] [AddCommGroup A]
    (j : I) (x : V → I → A) : (jointSumSplit j x).1 = fun v => ∑ i, x v i := by
  funext v
  exact sumSplit_first j (x v)

/-- Exact fiber counting for a coordinate of a finite product. -/
theorem uniform_first_coordinate {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Nonempty Ω] [Nonempty B]
    (e : Ω ≃ A × B) (a : A) :
    (FiniteProb.uniform Ω).prob (fun x => (e x).1 = a) =
      1 / (Fintype.card A : ℝ) := by
  let ef : {x : Ω // (e x).1 = a} ≃ B :=
    { toFun := fun x => (e x).2
      invFun := fun b => ⟨e.symm (a, b), by simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply e.injective
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext x.property.symm rfl
      right_inv := by intro b; simp }
  rw [FiniteProb.uniform_prob_eq_card]
  have hf : Fintype.card {x : Ω // (e x).1 = a} = Fintype.card B := Fintype.card_congr ef
  have hΩ : Fintype.card Ω = Fintype.card A * Fintype.card B := by
    simpa using Fintype.card_congr e
  rw [hf, hΩ, Nat.cast_mul]
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [one_mul] using (mul_div_mul_right (1 : ℝ) (Fintype.card A : ℝ) hB)

/-- The whole vector of sums is uniform, not merely each individual sum. -/
theorem outgoing_sums_jointly_uniform {V I A : Type*}
    [Fintype V] [Fintype I] [Fintype A] [AddCommGroup A]
    (j : I) (target : V → A) :
    (FiniteProb.uniform (V → I → A)).prob
      (fun x => (fun v => ∑ i, x v i) = target) =
        1 / (Fintype.card (V → A) : ℝ) := by
  have h := uniform_first_coordinate (jointSumSplit (V := V) (A := A) j) target
  simpa only [jointSumSplit_first] using h

/-- Symmetry of the extractor; the proof's distinguished edge is not an input. -/
theorem outgoing_sum_branch_invariant {I A : Type*} [Fintype I] [AddCommGroup A]
    (e : Equiv.Perm I) (x : I → A) : (∑ i, x (e i)) = ∑ i, x i :=
  Equiv.sum_comp e x

end
end MISLocal
