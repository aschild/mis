import MISLocal.ProjectedBudget

/-! Actual maximizing short lists and the pointwise bound outside them. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

variable {A : Type*} [Fintype A]

theorem exists_bestList (w : A → ℝ) (m : ℕ) :
    ∃ B : Finset A, B.card ≤ m ∧ ∀ S : Finset A, S.card ≤ m →
      (∑ a ∈ S, w a) ≤ ∑ a ∈ B, w a := by
  let choices := Finset.univ.powerset.filter (fun S : Finset A => S.card ≤ m)
  have he : (∅ : Finset A) ∈ choices := by simp [choices]
  obtain ⟨B, hB, hmax⟩ := choices.exists_max_image (fun S => ∑ a ∈ S, w a) ⟨∅,he⟩
  refine ⟨B, (Finset.mem_filter.mp hB).2, ?_⟩
  intro S hS
  exact hmax S (by simp [choices, hS])

def bestList (w : A → ℝ) (m : ℕ) : Finset A := (exists_bestList w m).choose

theorem bestList_card (w : A → ℝ) (m : ℕ) : (bestList w m).card ≤ m :=
  (exists_bestList w m).choose_spec.1

theorem bestList_optimal (w : A → ℝ) (m : ℕ) (S : Finset A) (hS : S.card ≤ m) :
    (∑ a ∈ S, w a) ≤ ∑ a ∈ bestList w m, w a :=
  (exists_bestList w m).choose_spec.2 S hS

theorem bestList_exchange (w : A → ℝ) (m : ℕ) {a b : A}
    (ha : a ∉ bestList w m) (hb : b ∈ bestList w m) : w a ≤ w b := by
  let B := bestList w m
  have hab : a ∉ B.erase b := fun h => ha (Finset.mem_erase.mp h).2
  have hc : (insert a (B.erase b)).card ≤ m := by
    rw [Finset.card_insert_of_not_mem hab, Finset.card_erase_of_mem hb]
    have hB := bestList_card w m
    have hpos := Finset.card_pos.mpr ⟨b,hb⟩
    dsimp [B] at *
    omega
  have h := bestList_optimal w m (insert a (B.erase b)) hc
  rw [Finset.sum_insert hab] at h
  have he := Finset.sum_erase_add B w hb
  change (∑ x ∈ B.erase b, w x) + w b = ∑ x ∈ bestList w m, w x at he
  linarith

theorem bestList_outside_zero_of_card_lt (w : A → ℝ) (m : ℕ)
    (hw : ∀ a, 0 ≤ w a) (hc : (bestList w m).card < m) {a : A}
    (ha : a ∉ bestList w m) : w a = 0 := by
  have hi : (insert a (bestList w m)).card ≤ m := by
    rw [Finset.card_insert_of_not_mem ha]
    omega
  have h := bestList_optimal w m _ hi
  rw [Finset.sum_insert ha] at h
  exact le_antisymm (by linarith) (hw a)

/-- Every omitted weight is at most total mass divided by the list capacity.
This includes the case where the capacity exceeds the entire alphabet. -/
theorem bestList_outside_le (w : A → ℝ) (m : ℕ) (hm : 0 < m)
    (hw : ∀ a, 0 ≤ w a) {a : A} (ha : a ∉ bestList w m) :
    w a ≤ (∑ b, w b) / (m : ℝ) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  by_cases hc : (bestList w m).card = m
  · have hs : (m:ℝ)*w a ≤ ∑ b ∈ bestList w m, w b := by
      calc
        _ = ∑ _b ∈ bestList w m, w a := by simp [hc]
        _ ≤ _ := Finset.sum_le_sum (fun b hb => bestList_exchange w m ha hb)
    have hall := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (bestList w m))
      (fun b _ _ => hw b)
    apply (le_div_iff₀ hm').mpr
    nlinarith [hs.trans hall]
  · have hc' : (bestList w m).card < m := lt_of_le_of_ne (bestList_card w m) hc
    rw [bestList_outside_zero_of_card_lt w m hw hc' ha]
    exact div_nonneg (Finset.sum_nonneg (fun b _ => hw b)) hm'.le

namespace FiniteProb

def outputList (μ : FiniteProb (Option A)) (m : ℕ) : Finset A :=
  bestList (fun a => μ.weight (some a)) m

def listTail (μ : FiniteProb (Option A)) (S : Finset A) : ℝ :=
  ∑ a ∈ Finset.univ \ S, μ.weight (some a)

def tail (μ : FiniteProb (Option A)) (m : ℕ) : ℝ := μ.listTail (μ.outputList m)

theorem listTail_eq (μ : FiniteProb (Option A)) (S : Finset A) :
    μ.listTail S = μ.prob (fun a => a ≠ none) - ∑ a ∈ S, μ.weight (some a) := by
  have h := Finset.sum_sdiff (f := fun a => μ.weight (some a)) (Finset.subset_univ S)
  rw [μ.occupied_mass] at h
  change μ.listTail S + (∑ a ∈ S, μ.weight (some a)) = _ at h
  linarith

theorem listTail_nonneg (μ : FiniteProb (Option A)) (S : Finset A) : 0 ≤ μ.listTail S :=
  Finset.sum_nonneg (fun a _ => μ.nonneg (some a))

theorem listTail_le_one (μ : FiniteProb (Option A)) (S : Finset A) : μ.listTail S ≤ 1 := by
  rw [μ.listTail_eq]
  have h := Finset.sum_nonneg (s := S) (fun a _ => μ.nonneg (some a))
  linarith [μ.prob_le_one (fun a => a ≠ none)]

theorem tail_minimal (μ : FiniteProb (Option A)) (m : ℕ) (S : Finset A) (hS : S.card ≤ m) :
    μ.tail m ≤ μ.listTail S := by
  unfold tail
  rw [μ.listTail_eq, μ.listTail_eq]
  have h := bestList_optimal (fun a => μ.weight (some a)) m S hS
  exact sub_le_sub_left h _

theorem outside_outputList_le (μ : FiniteProb (Option A)) (m : ℕ) (hm : 0 < m)
    {a : A} (ha : a ∉ μ.outputList m) : μ.weight (some a) ≤ 1/(m:ℝ) := by
  have h := bestList_outside_le (fun a => μ.weight (some a)) m hm (fun a => μ.nonneg _) ha
  rw [μ.occupied_mass] at h
  exact h.trans (div_le_div_of_nonneg_right (μ.prob_le_one _) (Nat.cast_nonneg _))

end FiniteProb
end
end MISLocal
