import MISLocal.SourceGrouping
import MISLocal.RevealedEntropy
import MISLocal.Conditioning

/-!
# Coordinate conditioning preserves a product distribution

On each positive observation fiber, observed coordinates become point masses
and the other coordinates keep their original distributions. The result
applies to arbitrary finite coordinate types and real probability weights.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem bit_forall {I : Type*} [Fintype I] (p : I → Prop) :
    bit (∀ i, p i) = ∏ i, bit (p i) := by
  by_cases h : ∀ i, p i
  · simp [bit, h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [show bit (∀ i, p i) = 0 by simp [bit, h]]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [bit, hi])

namespace FiniteProb

variable {I : Type*} [Fintype I] [DecidableEq I]
  {T : I → Type*} [∀ i, Fintype (T i)]

theorem pi_observe_probability (P : ∀ i, FiniteProb (T i))
    (S : Finset I) (x₀ : ∀ i, T i) :
    (pi P).prob (fun x => observeInputs S x = observeInputs S x₀) =
      ∏ i, if i ∈ S then (P i).weight (x₀ i) else 1 := by
  have hb (x : ∀ i, T i) : bit (observeInputs S x = observeInputs S x₀) =
      ∏ i, if i ∈ S then bit (x i = x₀ i) else 1 := by
    rw [show bit (observeInputs S x = observeInputs S x₀) = bit (∀ i, i ∈ S → x i = x₀ i) from
      congrArg bit (propext (observeInputs_eq_iff S x x₀)), bit_forall]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi, bit]
  change (pi P).expect _ = _
  rw [(pi P).expect_congr hb, expect_pi_prod P
    (fun i a => if i ∈ S then bit (a = x₀ i) else 1)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [hi, expect, bit]
  · simp [hi]

def pinInputs (P : ∀ i, FiniteProb (T i)) (S : Finset I) (x₀ : ∀ i, T i) :
    ∀ i, FiniteProb (T i) := fun i => if i ∈ S then pointMass (x₀ i) else P i

theorem given_observe_eq_pi (P : ∀ i, FiniteProb (T i)) (S : Finset I) (x₀ : ∀ i, T i)
    (hb : 0 < ((pi P).map (observeInputs S)).weight (observeInputs S x₀)) :
    (pi P).given (observeInputs S) (observeInputs S x₀) = pi (pinInputs P S x₀) := by
  have hprob : ((pi P).map (observeInputs S)).weight (observeInputs S x₀) =
      ∏ i, if i ∈ S then (P i).weight (x₀ i) else 1 := pi_observe_probability P S x₀
  ext x
  rw [given_weight _ _ _ hb]
  by_cases hx : observeInputs S x = observeInputs S x₀
  · have hfactor : (pi P).weight x =
        ((pi P).map (observeInputs S)).weight (observeInputs S x₀) *
          (pi (pinInputs P S x₀)).weight x := by
      rw [hprob]
      change (∏ i, (P i).weight (x i)) =
        (∏ i, if i ∈ S then (P i).weight (x₀ i) else 1) *
          ∏ i, (pinInputs P S x₀ i).weight (x i)
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · have heq := (observeInputs_eq_iff S x x₀).mp hx i hi
        simp [pinInputs, hi, pointMass, bit, heq]
      · simp [pinInputs, hi]
    rw [hfactor]
    simp [bit, hx, ne_of_gt hb]
  · have hx' : ∃ i, i ∈ S ∧ x i ≠ x₀ i := by
      by_contra hn
      apply hx
      apply (observeInputs_eq_iff S x x₀).mpr
      intro i hi
      by_contra he
      exact hn ⟨i,hi,he⟩
    obtain ⟨i,hi,hxi⟩ := hx'
    have hzero : (pi (pinInputs P S x₀)).weight x = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [pinInputs, hi, pointMass, bit, hxi]
    simp [bit, hx, hzero]

theorem map_positive_has_preimage {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ : FiniteProb Ω) (X : Ω → A) (a : A) (ha : 0 < (μ.map X).weight a) :
    ∃ ω, X ω = a := by
  by_contra hn
  have he : μ.prob (fun ω => X ω = a) = 0 := by
    rw [μ.prob_congr (q := fun _ => False) (by
      intro ω
      exact ⟨fun h => hn ⟨ω,h⟩, False.elim⟩), prob_false]
  change 0 < μ.prob (fun ω => X ω = a) at ha
  linarith

/-- No assertion is made for null fibers, where `given` uses its documented
fallback distribution. All probabilistic uses average with the fiber weight. -/
theorem given_observe_is_product (P : ∀ i, FiniteProb (T i)) (S : Finset I)
    (y : ∀ i, Option (T i)) (hy : 0 < ((pi P).map (observeInputs S)).weight y) :
    ∃ Q : ∀ i, FiniteProb (T i), (pi P).given (observeInputs S) y = pi Q := by
  obtain ⟨x,hx⟩ := (pi P).map_positive_has_preimage (observeInputs S) y hy
  refine ⟨pinInputs P S x, ?_⟩
  rw [← hx]
  exact given_observe_eq_pi P S x (by rwa [hx])

theorem conditional_disjoint_blocks_independent {J : Type*} [Fintype J] [DecidableEq J]
    {B : J → Type*} (P : ∀ i, FiniteProb (T i)) (S : Finset I)
    (y : ∀ i, Option (T i)) (hy : 0 < ((pi P).map (observeInputs S)).weight y)
    (owner : I → Option J) (f : ∀ j, (∀ i : {i // owner i = some j}, T i.val) → B j) :
    ((pi P).given (observeInputs S) y).Independent (fun j x => f j (fun i => x i.val)) := by
  obtain ⟨Q,hQ⟩ := given_observe_is_product P S y hy
  rw [hQ]
  exact disjoint_blocks_independent Q owner f

end FiniteProb
end
end MISLocal
