import MISLocal.ProductSources

/-! Disjoint groups of independent coordinates remain jointly independent. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def groupInputs {S J : Type*} {T : S → Type*} (owner : S → J) :
    (∀ s, T s) ≃ (∀ j, ∀ s : {s // owner s = j}, T s.val) where
  toFun x _ s := x s.val
  invFun x s := x (owner s) ⟨s,rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext j s
    rcases s with ⟨s,hs⟩
    cases hs
    rfl

namespace FiniteProb

variable {S J : Type*} {T : S → Type*} [Fintype S] [Fintype J] [∀ s, Fintype (T s)]
  [DecidableEq S] [DecidableEq J]

theorem pi_grouped (P : ∀ s, FiniteProb (T s)) (owner : S → J) :
    (pi P).map (groupInputs (T := T) owner) =
      pi (fun j => pi (fun s : {s // owner s = j} => P s.val)) := by
  ext x
  rw [map_equiv_weight]
  change (∏ s, (P s).weight (x (owner s) ⟨s,rfl⟩)) =
    ∏ j, ∏ s : {s // owner s = j}, (P s.val).weight (x j s)
  rw [← Fintype.prod_fiberwise owner (fun s => (P s).weight (x (owner s) ⟨s,rfl⟩))]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  rintro ⟨s,hs⟩ _
  cases hs
  rfl

theorem grouped_independent (P : ∀ s, FiniteProb (T s)) (owner : S → J) :
    (pi P).Independent (fun j x => (fun s : {s // owner s = j} => x s.val)) := by
  have h : ((pi P).map (groupInputs (T := T) owner)).Independent (fun j x => x j) := by
    rw [pi_grouped]
    exact pi_independent _
  simpa only [Independent, expect_map] using h

theorem Independent.option_some {Ω I : Type*} [Fintype Ω] [Fintype I]
    {T : Option I → Type*} {μ : FiniteProb Ω} {X : ∀ i, Ω → T i}
    (h : μ.Independent X) : μ.Independent (fun i : I => X (some i)) := by
  intro f
  have he := h (fun i => match i with | none => fun _ => (1:ℝ) | some i => f i)
  simpa only [Fintype.prod_option, one_mul, expect_const] using he

/-- Coordinates with owner `none` may contain private randomness or unused
inputs. Arbitrary functions of the disjoint remaining blocks are independent. -/
theorem disjoint_blocks_independent {B : J → Type*} (P : ∀ s, FiniteProb (T s))
    (owner : S → Option J) (f : ∀ j, (∀ s : {s // owner s = some j}, T s.val) → B j) :
    (pi P).Independent (fun j x => f j (fun s => x s.val)) :=
  ((grouped_independent P owner).option_some).comp f

end FiniteProb
end
end MISLocal
