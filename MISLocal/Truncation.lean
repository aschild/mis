import MISLocal.BranchTransfer
import MISLocal.DenseMatrix

/-! Actual kept/deleted outputs and their conditional atom bounds. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def restrictOutput {A : Type*} (P : A → Prop) (x : Option A) : Option A :=
  match x with
  | none => none
  | some a => if P a then some a else none

theorem restrictOutput_eq_some {A : Type*} (P : A → Prop) (x : Option A) (a : A) :
    restrictOutput P x = some a ↔ x = some a ∧ P a := by
  cases x with
  | none => simp [restrictOutput]
  | some b =>
    by_cases hba : b = a
    · subst b
      by_cases ha : P a <;> simp [restrictOutput, ha]
    · by_cases hb : P b <;> simp [restrictOutput, hb, hba]

theorem restrictOutput_partition {A : Type*} (P : A → Prop) (x : Option A) :
    bit (restrictOutput P x ≠ none) + bit (restrictOutput (fun a => ¬P a) x ≠ none) =
      bit (x ≠ none) := by
  cases x with
  | none => simp [restrictOutput, bit]
  | some a => by_cases h : P a <;> simp [restrictOutput, bit, h]

theorem restricted_conflicts {A B : Type*} (E : A → B → Prop)
    (P : A → Prop) (Q : B → Prop) (x : Option A) (y : Option B) :
    bit (selectedConflict (fun _ : Unit => E) ((), restrictOutput P x, restrictOutput Q y)) +
      bit (selectedConflict (fun _ : Unit => E)
        ((), restrictOutput (fun a => ¬ P a) x, restrictOutput (fun b => ¬ Q b) y)) ≤
      bit (selectedConflict (fun _ : Unit => E) ((),x,y)) := by
  cases x with
  | none => simp [restrictOutput, selectedConflict, bit]
  | some a =>
    cases y with
    | none => simp [restrictOutput, selectedConflict, bit]
    | some b =>
      by_cases hp : P a <;> by_cases hq : Q b <;> by_cases he : E a b <;>
        simp [restrictOutput, selectedConflict, bit, hp, hq, he]

namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem given_support_eq (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) {ω : Ω} (hω : 0 < (μ.given Y b).weight ω) :
    Y ω = b := by
  by_contra h
  rw [given_weight μ Y b hb] at hω
  simp [bit, h] at hω

theorem given_prob_congr (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) (E F : Ω → Prop)
    (h : ∀ ω, Y ω = b → (E ω ↔ F ω)) :
    (μ.given Y b).prob E = (μ.given Y b).prob F := by
  apply (μ.given Y b).expect_congr_on_support
  intro ω hω
  exact congrArg bit (propext (h ω (μ.given_support_eq Y b hb hω)))

def keptOutput (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B) (m : ℕ) (ω : Ω) : Option A :=
  restrictOutput (fun a => a ∈ ((μ.given Y (Y ω)).map Z).outputList m) (Z ω)

def deletedOutput (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B) (m : ℕ) (ω : Ω) : Option A :=
  restrictOutput (fun a => a ∉ ((μ.given Y (Y ω)).map Z).outputList m) (Z ω)

theorem kept_deleted_mass (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B) (m : ℕ) :
    μ.prob (fun ω => μ.keptOutput Z Y m ω ≠ none) +
      μ.prob (fun ω => μ.deletedOutput Z Y m ω ≠ none) = μ.prob (fun ω => Z ω ≠ none) := by
  rw [prob, prob, ← μ.expect_add]
  exact μ.expect_congr (fun ω => restrictOutput_partition _ (Z ω))

theorem deleted_given_atom (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B)
    (m : ℕ) (b : B) (hb : 0 < (μ.map Y).weight b) (a : A) :
    ((μ.given Y b).map (μ.deletedOutput Z Y m)).weight (some a) =
      if a ∈ ((μ.given Y b).map Z).outputList m then 0 else ((μ.given Y b).map Z).weight (some a) := by
  change (μ.given Y b).prob (fun ω => μ.deletedOutput Z Y m ω = some a) = _
  rw [μ.given_prob_congr Y b hb _ (fun ω => Z ω = some a ∧ a ∉ ((μ.given Y b).map Z).outputList m)
    (by intro ω hω; simp only [deletedOutput, hω, restrictOutput_eq_some])]
  by_cases ha : a ∈ ((μ.given Y b).map Z).outputList m
  · simp only [ha, not_true_eq_false, and_false, if_true, prob_false]
  · simp only [ha, not_false_eq_true, and_true, if_false]
    rfl

theorem deleted_given_atom_le (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B)
    {m : ℕ} (hm : 0 < m) (b : B) (hb : 0 < (μ.map Y).weight b) (a : A) :
    ((μ.given Y b).map (μ.deletedOutput Z Y m)).weight (some a) ≤ 1/(m : ℝ) := by
  rw [μ.deleted_given_atom Z Y m b hb a]
  by_cases ha : a ∈ ((μ.given Y b).map Z).outputList m
  · simp only [ha, if_true]; positivity
  · simp only [ha, if_false]
    exact outside_outputList_le _ m hm ha

theorem kept_given_support (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B)
    (m : ℕ) (b : B) (hb : 0 < (μ.map Y).weight b) (a : A)
    (ha : a ∉ ((μ.given Y b).map Z).outputList m) :
    ((μ.given Y b).map (μ.keptOutput Z Y m)).weight (some a) = 0 := by
  change (μ.given Y b).prob (fun ω => μ.keptOutput Z Y m ω = some a) = _
  rw [μ.given_prob_congr Y b hb _ (fun _ => False) (by
    intro ω hω
    simp only [keptOutput, hω, restrictOutput_eq_some, ha, and_false])]
  exact prob_false _

theorem tail_lower_of_atom_bound (P : FiniteProb (Option A)) (M : ℕ) {c : ℝ}
    (hc : 0 ≤ c) (hatom : ∀ a, P.weight (some a) ≤ c) :
    P.prob (fun a => a ≠ none) - (M : ℝ)*c ≤ P.tail M := by
  change _ ≤ P.listTail (P.outputList M)
  rw [P.listTail_eq]
  have hs := Finset.sum_le_sum (s := P.outputList M) (fun a _ => hatom a)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hcard : ((P.outputList M).card : ℝ) ≤ M := by exact_mod_cast bestList_card _ M
  have hm := mul_le_mul_of_nonneg_right hcard hc
  linarith

theorem deleted_given_tail_lower (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B)
    {m : ℕ} (hm : 0 < m) (M : ℕ) (b : B) (hb : 0 < (μ.map Y).weight b) :
    (μ.given Y b).prob (fun ω => μ.deletedOutput Z Y m ω ≠ none) - (M : ℝ)/m ≤
      ((μ.given Y b).map (μ.deletedOutput Z Y m)).tail M := by
  have h := (((μ.given Y b).map (μ.deletedOutput Z Y m))).tail_lower_of_atom_bound M
    (show 0 ≤ (1:ℝ)/m by positivity) (μ.deleted_given_atom_le Z Y hm b hb)
  simpa [prob_map, div_eq_mul_inv] using h

end FiniteProb
end
end MISLocal
