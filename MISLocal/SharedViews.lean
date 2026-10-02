import MISLocal.ConditionalSources
import MISLocal.Truncation

/-! Conditional independence from disjoint coordinate dependencies. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def ReadsOnly {I A : Type*} {T : I → Type*} (Y : (∀ i, T i) → A) (S : Finset I) : Prop :=
  ∀ x z, (∀ i ∈ S, x i = z i) → Y x = Y z

theorem ReadsOnly.doesNotRead {I A : Type*} {T : I → Type*}
    {Y : (∀ i, T i) → A} {S : Finset I} (h : ReadsOnly Y S) (i : I) (hi : i ∉ S) :
    FiniteProb.DoesNotRead Y i := by
  intro x z hxz
  apply h
  intro j hj
  exact hxz j (fun hji => hi (hji ▸ hj))

namespace FiniteProb

theorem Independent.congr_on_support {Ω J : Type*} [Fintype Ω] [Fintype J]
    {B : J → Type*} {μ : FiniteProb Ω} {X Y : ∀ j, Ω → B j}
    (h : μ.Independent X) (hXY : ∀ j ω, 0 < μ.weight ω → X j ω = Y j ω) : μ.Independent Y := by
  intro f
  calc
    _ = μ.expect (fun ω => ∏ j, f j (X j ω)) := by
      apply μ.expect_congr_on_support
      intro ω hω
      exact Finset.prod_congr rfl (fun j _ => congrArg (f j) (hXY j ω hω).symm)
    _ = ∏ j, μ.expect (fun ω => f j (X j ω)) := h f
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      apply μ.expect_congr_on_support
      intro ω hω
      exact congrArg (f j) (hXY j ω hω)

/-- Variables may share arbitrary observed coordinates. Outside the observed
set their read sets must be pairwise disjoint. Conditional independence then
follows from the actual product input distribution. -/
theorem conditional_independent_of_disjoint_reads
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {T : I → Type*} [∀ i, Fintype (T i)] {B : J → Type*}
    (P : ∀ i, FiniteProb (T i)) (Y : ∀ j, (∀ i, T i) → B j)
    (reads : J → Finset I) (S : Finset I)
    (hlocal : ∀ j, ReadsOnly (Y j) (reads j))
    (hdisjoint : ∀ j k, j ≠ k → ∀ i, i ∈ reads j → i ∈ reads k → i ∈ S)
    (y : ∀ i, Option (T i)) (hy : 0 < ((pi P).map (observeInputs S)).weight y) :
    ((pi P).given (observeInputs S) y).Independent Y := by
  obtain ⟨x₀,hx₀⟩ := (pi P).map_positive_has_preimage (observeInputs S) y hy
  let owner : I → Option J := fun i =>
    if h : ∃ j, i ∈ reads j ∧ i ∉ S then some h.choose else none
  have howner (j : J) (i : I) (hi : i ∈ reads j) (hiS : i ∉ S) : owner i = some j := by
    have hex : ∃ k, i ∈ reads k ∧ i ∉ S := ⟨j,hi,hiS⟩
    have heq : hex.choose = j := by
      by_contra hn
      exact hiS (hdisjoint hex.choose j hn i hex.choose_spec.1 hi)
    simp [owner, hex, heq]
  let f : ∀ j, (∀ i : {i // owner i = some j}, T i.val) → B j :=
    fun j z => Y j (fun i => if h : owner i = some j then z ⟨i,h⟩ else x₀ i)
  have hblock := conditional_disjoint_blocks_independent P S y hy owner f
  apply hblock.congr_on_support
  intro j x hx
  symm
  apply hlocal j
  intro i hi
  have hxy : observeInputs S x = observeInputs S x₀ :=
    ((pi P).given_support_eq (observeInputs S) y hy hx).trans hx₀.symm
  by_cases hiS : i ∈ S
  · have hv := (observeInputs_eq_iff S x x₀).mp hxy i hiS
    dsimp
    split_ifs <;> simp_all
  · have ho := howner j i hi hiS
    dsimp
    simp only [ho, dite_true, if_true]

theorem independent_bool_pair_distribution {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ : FiniteProb Ω) (Y : Bool → Ω → A) (h : μ.Independent Y) :
    μ.map (fun ω => (Y false ω,Y true ω)) = (μ.map (Y false)).product (μ.map (Y true)) := by
  ext ab
  have hf := h (fun b a => bit (a = if b then ab.2 else ab.1))
  simp only [Fintype.prod_bool, Bool.false_eq_true, if_false, if_true] at hf
  change μ.expect (fun ω => bit ((Y false ω,Y true ω) = ab)) =
    μ.expect (fun ω => bit (Y false ω = ab.1)) * μ.expect (fun ω => bit (Y true ω = ab.2))
  have he (ω : Ω) : bit ((Y false ω,Y true ω) = ab) =
      bit (Y false ω = ab.1)*bit (Y true ω = ab.2) := by
    by_cases h0 : Y false ω = ab.1 <;> by_cases h1 : Y true ω = ab.2 <;>
      simp [bit, Prod.ext_iff, h0, h1]
  rw [μ.expect_congr he]
  simpa only [mul_comm] using hf

end FiniteProb
end
end MISLocal
