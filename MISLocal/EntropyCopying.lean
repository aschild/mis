import MISLocal.ConditionalEntropy

/-!
# The information-copying step used by the tree entropy proof

This is a theorem about actual Shannon entropies of arbitrary finite random
variables. A destination state Y receives W = f(S) from a source edge state S.
The source edge gains no entropy. Each other incident edge gains at most
H(W | Y), exactly offset by the vertex term.

It does not assert that the required copying schedule has been constructed
on the infinite regular tree; that geometric construction remains separate.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C E I : Type*}
  [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype I]

theorem source_edge_copy_entropy (μ : FiniteProb Ω)
    (S : Ω → A) (Y : Ω → B) (f : A → C) :
    μ.entropyOf (fun ω => ((f (S ω), Y ω), S ω)) =
      μ.entropyOf (fun ω => (Y ω, S ω)) := by
  apply μ.entropyOf_comp_injective (fun ω => (Y ω, S ω))
    (fun p : B × A => ((f p.2, p.1), p.2))
  intro p q h
  exact Prod.ext (congrArg (fun t : (C × B) × A => t.1.2) h)
    (congrArg (fun t : (C × B) × A => t.2) h)

theorem other_edge_copy_entropy (μ : FiniteProb Ω)
    (W : Ω → C) (Y : Ω → B) (Z : Ω → E) :
    μ.entropyOf (fun ω => ((W ω,Y ω),Z ω)) - μ.entropyOf (fun ω => (Y ω,Z ω)) ≤
      μ.entropyOf (fun ω => (W ω,Y ω)) - μ.entropyOf Y := by
  rw [μ.entropy_pair_assoc]
  exact μ.conditioning_reduces W Y Z

/-- Exact local change in the edge-minus-vertex entropy potential is nonpositive.
The number of OTHER edges is `card I`; thus on a D-regular tree it is D-1.
There is no natural-number subtraction in this statement. -/
theorem copying_potential_nonincrease (μ : FiniteProb Ω)
    (S : Ω → A) (Y : Ω → B) (f : A → C) (Z : I → Ω → E) :
    (μ.entropyOf (fun ω => ((f (S ω),Y ω),S ω)) -
        μ.entropyOf (fun ω => (Y ω,S ω))) +
      (∑ i, (μ.entropyOf (fun ω => ((f (S ω),Y ω),Z i ω)) -
        μ.entropyOf (fun ω => (Y ω,Z i ω)))) -
      (Fintype.card I : ℝ) *
        (μ.entropyOf (fun ω => (f (S ω),Y ω)) - μ.entropyOf Y) ≤ 0 := by
  rw [μ.source_edge_copy_entropy S Y f, sub_self, zero_add]
  apply sub_nonpos.mpr
  calc
    _ ≤ ∑ _i : I, (μ.entropyOf (fun ω => (f (S ω),Y ω)) - μ.entropyOf Y) := by
      apply Finset.sum_le_sum
      intro i _
      exact μ.other_edge_copy_entropy (fun ω => f (S ω)) Y (Z i)
    _ = _ := by simp [mul_sub]

end FiniteProb

/-- Cancellation of raw-input entropy after the neighborhood counts are known.
The common factor g may be enormous; it cancels identically. -/
theorem raw_tree_entropy_cancellation (D g : ℝ) (h : ℕ) :
    D / 2 * (1 + 2 * ∑ i ∈ Finset.range h, (D-1)^(i+1)) * g -
      (D-1) * (D * ∑ i ∈ Finset.range h, (D-1)^i) * g - D/2*g = 0 := by
  simp only [pow_succ, ← Finset.sum_mul]
  ring

/-- Numerical endpoint of the copying argument, with its schedule inequality
explicit. This is NOT a theorem constructing that schedule on a regular tree. -/
theorem tree_entropy_from_copying_endpoints {D Hvertex Hedge K : ℝ}
    (hcopy : K ≤ D / 2 * Hedge - (D-1) * Hvertex) :
    D / 2 * Hedge ≥ (D-1) * Hvertex + K := by linarith

end
end MISLocal
