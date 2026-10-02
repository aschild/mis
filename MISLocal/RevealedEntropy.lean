import MISLocal.ProductSources

/-!
# Revealing finitely many independent sources

Observations are literal coordinate restrictions, represented by `Option` at
each coordinate. Revealing a source is set insertion; every entropy identity
is proved for this representation and the actual product probability space.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

variable {I : Type*} [DecidableEq I] {T : I → Type*}

def observeInputs (S : Finset I) (x : ∀ i, T i) : ∀ i, Option (T i) :=
  fun i => if i ∈ S then some (x i) else none

theorem observeInputs_eq_iff (S : Finset I) (x y : ∀ i, T i) :
    observeInputs S x = observeInputs S y ↔ ∀ i ∈ S, x i = y i := by
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa only [observeInputs, hi, if_true, Option.some.injEq] using he
  · intro h
    funext i
    by_cases hi : i ∈ S <;> simp [observeInputs, hi, h i]

theorem observeInputs_insert_fibers (S : Finset I) (i : I) (x y : ∀ i, T i) :
    observeInputs (insert i S) x = observeInputs (insert i S) y ↔
      (observeInputs S x,x i) = (observeInputs S y,y i) := by
  simp only [observeInputs_eq_iff, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Finset.mem_insert_of_mem hj), h i (Finset.mem_insert_self _ _)⟩
  · rintro ⟨hS,hi⟩ j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact hS j hj

theorem observeInputs_doesNotRead (S : Finset I) (i : I) (hi : i ∉ S) :
    FiniteProb.DoesNotRead (observeInputs (T := T) S) i := by
  intro x y hxy
  apply (observeInputs_eq_iff S x y).mpr
  intro j hj
  exact hxy j (fun h => hi (h ▸ hj))

namespace FiniteProb

variable [Fintype I] [∀ i, Fintype (T i)] {A B : Type*} [Fintype A] [Fintype B]

def revealGain (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) : ℝ :=
  (pi P).condEntropy Y (observeInputs S) - (pi P).condEntropy Y (observeInputs (insert i S))

theorem revealGain_eq (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) :
    revealGain P Y S i = (pi P).condEntropy Y (observeInputs S) -
      (pi P).condEntropy Y (fun x => (observeInputs S x,x i)) := by
  unfold revealGain
  rw [(pi P).condEntropy_same_fibers Y _ _ (observeInputs_insert_fibers S i)]

theorem revealGain_nonneg (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) : 0 ≤ revealGain P Y S i := by
  rw [revealGain_eq]
  exact (pi P).reveal_gain_nonneg Y (fun x => x i) (observeInputs S)

theorem revealGain_known (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) (hi : i ∈ S) : revealGain P Y S i = 0 := by
  simp only [revealGain, Finset.insert_eq_of_mem hi, sub_self]

theorem revealGain_unread (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) (hY : DoesNotRead Y i) : revealGain P Y S i = 0 := by
  by_cases hi : i ∈ S
  · exact revealGain_known P Y S i hi
  · rw [revealGain_eq, (pi P).reveal_gain_symm]
    rw [coordinate_condEntropy P i _ (observeInputs_doesNotRead S i hi),
      coordinate_condEntropy P i _ (by
        intro x y hxy
        exact Prod.ext (observeInputs_doesNotRead S i hi x y hxy) (hY x y hxy)), sub_self]

/-- On an edge that has not already observed the source, revealing that
source yields at least the gain at either endpoint. -/
theorem revealGain_refinement (P : ∀ i, FiniteProb (T i))
    (Y : (∀ i, T i) → A) (W : (∀ i, T i) → B)
    (S U : Finset I) (i : I) (hSU : S ⊆ U) (hi : i ∉ U)
    (hYW : ∀ x y, W x = W y → Y x = Y y) :
    revealGain P Y S i ≤ revealGain P W U i := by
  have hiS : i ∉ S := fun h => hi (hSU h)
  rw [revealGain_eq, revealGain_eq,
    (pi P).reveal_gain_symm Y (fun x => x i) (observeInputs S),
    (pi P).reveal_gain_symm W (fun x => x i) (observeInputs U),
    coordinate_condEntropy P i _ (observeInputs_doesNotRead S i hiS),
    coordinate_condEntropy P i _ (observeInputs_doesNotRead U i hi)]
  apply sub_le_sub_left
  apply (pi P).condEntropy_refinement
  intro x y he
  refine Prod.ext ?_ (hYW x y (congrArg Prod.snd he))
  apply (observeInputs_eq_iff S x y).mpr
  intro j hj
  exact (observeInputs_eq_iff U x y).mp (congrArg Prod.fst he) j (hSU hj)

end FiniteProb

def revealPrefix {n : ℕ} (t : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < t)

@[simp] theorem revealPrefix_zero {n : ℕ} : revealPrefix (n := n) 0 = ∅ := by
  ext i
  simp [revealPrefix]

@[simp] theorem revealPrefix_full (n : ℕ) : revealPrefix (n := n) n = Finset.univ := by
  ext i
  simp [revealPrefix, i.isLt]

theorem revealPrefix_succ {n : ℕ} (i : Fin n) :
    revealPrefix (i.val+1) = insert i (revealPrefix i.val) := by
  ext j
  simp only [revealPrefix, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

theorem self_not_revealPrefix {n : ℕ} (i : Fin n) : i ∉ revealPrefix i.val := by
  simp [revealPrefix]

namespace FiniteProb

theorem revealGain_sum {n : ℕ} {T : Fin n → Type*} [∀ i, Fintype (T i)]
    {A : Type*} [Fintype A] (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset (Fin n)) :
    (∑ i, revealGain P Y (S ∪ revealPrefix i.val) i) = (pi P).condEntropy Y (observeInputs S) := by
  let f : ℕ → ℝ := fun t => (pi P).condEntropy Y (observeInputs (S ∪ revealPrefix t))
  have he (i : Fin n) : revealGain P Y (S ∪ revealPrefix i.val) i = f i.val-f (i.val+1) := by
    simp only [revealGain, f, revealPrefix_succ, Finset.union_insert]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun t => f t-f (t+1)) n, Finset.sum_range_sub']
  have hfull : f n = 0 := by
    change (pi P).condEntropy Y (observeInputs (S ∪ revealPrefix n)) = 0
    rw [revealPrefix_full, Finset.union_eq_right.mpr (Finset.subset_univ S)]
    apply (pi P).condEntropy_of_determined
    intro x y hxy
    have heq : x = y := funext (fun i => (observeInputs_eq_iff Finset.univ x y).mp hxy i (Finset.mem_univ i))
    exact congrArg Y heq
  rw [hfull, sub_zero]
  simp [f]

end FiniteProb
end
end MISLocal
