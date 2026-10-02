import MISLocal.EntropyProduct

/-! Independence of one source from arbitrary functions of all other sources. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C I : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
  [Fintype I] [DecidableEq I]

theorem nonempty (P : FiniteProb Ω) : Nonempty Ω := by
  by_contra h
  haveI : IsEmpty Ω := not_nonempty_iff.mp h
  have ht := P.total
  simp at ht

theorem map_equiv_weight (μ : FiniteProb Ω) (e : Ω ≃ A) (a : A) :
    (μ.map e).weight a = μ.weight (e.symm a) := by
  change μ.prob (fun ω => e ω = a) = _
  rw [μ.prob_congr (fun ω => e.apply_eq_iff_eq_symm_apply)]
  simp [prob, expect, bit]

theorem entropyOf_map (μ : FiniteProb Ω) (X : Ω → A) (f : A → B) :
    (μ.map X).entropyOf f = μ.entropyOf (fun ω => f (X ω)) := by
  unfold entropyOf
  rw [map_comp]

theorem condEntropy_map (μ : FiniteProb Ω) (X : Ω → A) (f : A → B) (g : A → C) :
    (μ.map X).condEntropy f g = μ.condEntropy (fun ω => f (X ω)) (fun ω => g (X ω)) := by
  simp only [condEntropy, entropyOf_map]

theorem pi_splitAt {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (i : I) :
    (pi P).map (Equiv.piSplitAt i T) =
      (P i).product (pi (fun j : {j // j ≠ i} => P j.val)) := by
  ext ab
  rw [map_equiv_weight]
  change (∏ j, (P j).weight ((Equiv.piSplitAt i T).symm ab j)) =
    (P i).weight ab.1 * ∏ j : {j // j ≠ i}, (P j.val).weight (ab.2 j)
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  congr 1
  · simp [Equiv.piSplitAt]
  · apply Finset.prod_congr rfl
    intro j _
    simp [Equiv.piSplitAt, j.property]

theorem product_map_second (P : FiniteProb A) (Q : FiniteProb B) (f : B → C) :
    (P.product Q).map (fun ab => (ab.1,f ab.2)) = P.product (Q.map f) := by
  ext ac
  change (P.product Q).expect (fun ab => bit ((ab.1,f ab.2) = ac)) = _
  rw [product_expect]
  have he (a : A) (b : B) : bit ((a,f b) = ac) = bit (a = ac.1) * bit (f b = ac.2) := by
    by_cases ha : a = ac.1 <;> by_cases hb : f b = ac.2 <;> simp [bit, Prod.ext_iff, ha, hb]
  simp only [he, expect_mul]
  change P.expect (fun a => bit (a = ac.1) * (Q.map f).weight ac.2) = _
  simp [expect, bit, product]

theorem product_condEntropy_first_second (P : FiniteProb A) (Q : FiniteProb B) (f : B → C) :
    (P.product Q).condEntropy Prod.fst (fun ab => f ab.2) = P.entropy := by
  have hg : (P.product Q).map (fun ab => f ab.2) = Q.map f := by
    rw [← map_comp _ Prod.snd f, product_map_snd]
  simp only [condEntropy, entropyOf, product_map_second, hg, product_entropy]
  ring

/-- A source does not influence a function when changing only that source
leaves the function unchanged. This is a pointwise locality statement. -/
def DoesNotRead {T : I → Type*} (Y : (∀ i, T i) → A) (i : I) : Prop :=
  ∀ x y, (∀ j, j ≠ i → x j = y j) → Y x = Y y

theorem coordinate_condEntropy {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (i : I) (Y : (∀ i, T i) → A)
    (hY : DoesNotRead Y i) :
    (pi P).condEntropy (fun x => x i) Y = (P i).entropy := by
  let ai : T i := Classical.choice (P i).nonempty
  let f : (∀ j : {j // j ≠ i}, T j.val) → A :=
    fun z => Y ((Equiv.piSplitAt i T).symm (ai,z))
  have hf (x : ∀ i, T i) : Y x = f (fun j => x j.val) := by
    apply hY
    intro j hj
    simp [Equiv.piSplitAt, hj]
  have hm := (pi P).condEntropy_map (Equiv.piSplitAt i T) Prod.fst (fun ab => f ab.2)
  rw [pi_splitAt, product_condEntropy_first_second] at hm
  have he : (fun x => f (fun j => x j.val)) = Y := funext (fun x => (hf x).symm)
  simpa only [Equiv.piSplitAt_apply, he] using hm.symm

theorem condEntropy_same_fibers (μ : FiniteProb Ω) (X : Ω → A)
    (Y : Ω → B) (Z : Ω → C) (h : ∀ ω ω', Y ω = Y ω' ↔ Z ω = Z ω') :
    μ.condEntropy X Y = μ.condEntropy X Z := by
  have hj := μ.entropyOf_same_fibers (fun ω => (X ω,Y ω)) (fun ω => (X ω,Z ω))
    (by intro ω ω'; simp only [Prod.mk.injEq, h ω ω'])
  simp only [condEntropy, hj, μ.entropyOf_same_fibers Y Z h]

/-- Conditioning on finer data reduces entropy. Refinement is expressed by
equality of observations, avoiding arbitrary choices on unattained values. -/
theorem condEntropy_refinement (μ : FiniteProb Ω) (X : Ω → A)
    (Y : Ω → B) (Z : Ω → C) (h : ∀ ω ω', Z ω = Z ω' → Y ω = Y ω') :
    μ.condEntropy X Z ≤ μ.condEntropy X Y := by
  have he := μ.condEntropy_same_fibers X (fun ω => (Y ω,Z ω)) Z (by
    intro ω ω'
    simp only [Prod.mk.injEq]
    exact ⟨And.right, fun hz => ⟨h ω ω' hz,hz⟩⟩)
  rw [← he]
  exact μ.conditioning_reduces X Y Z

theorem condEntropy_of_determined (μ : FiniteProb Ω) (X : Ω → A)
    (Y : Ω → B) (h : ∀ ω ω', Y ω = Y ω' → X ω = X ω') :
    μ.condEntropy X Y = 0 := by
  have he := μ.entropyOf_same_fibers (fun ω => (X ω,Y ω)) Y (by
    intro ω ω'
    simp only [Prod.mk.injEq]
    exact ⟨And.right, fun hy => ⟨h ω ω' hy,hy⟩⟩)
  simp only [condEntropy, he, sub_self]

end FiniteProb
end
end MISLocal
