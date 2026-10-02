import MISLocal.Truncation
import MISLocal.SharedViews

/-! Constructed first-deletion parts of the original output. These are not
the realized resampled draws. Their conditional distributions will be used
to define the successive smaller-radius stochastic rules. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem restrictOutput_some_original {A : Type*} (P : A → Prop) (x : Option A)
    {a : A} (h : restrictOutput P x = some a) : x = some a :=
  (restrictOutput_eq_some P x a).mp h |>.1

theorem selectedConflict_of_restriction {C A B : Type*} (E : C → A → B → Prop)
    (c : C) (u u' : Option A) (v v' : Option B)
    (hu : ∀ a, u' = some a → u = some a) (hv : ∀ b, v' = some b → v = some b) :
    selectedConflict E (c,u',v') → selectedConflict E (c,u,v) := by
  cases u' with
  | none => simp [selectedConflict]
  | some a =>
    cases v' with
    | none => simp [selectedConflict]
    | some b => simp [selectedConflict, hu a rfl, hv b rfl]

namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

def survivor (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m : ℕ) :
    ℕ → Ω → Option A
  | 0 => U
  | n+1 => μ.keptOutput (μ.survivor U Y m n) (Y n) m

def firstDeleted (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m n : ℕ) :
    Ω → Option A := μ.deletedOutput (μ.survivor U Y m n) (Y n) m

theorem survivor_some_original (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (ω : Ω) (a : A) :
    μ.survivor U Y m n ω = some a → U ω = some a := by
  induction n with
  | zero => exact id
  | succ n ih =>
    intro h
    exact ih (restrictOutput_some_original _ _ h)

theorem firstDeleted_some_survivor (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (ω : Ω) (a : A) :
    μ.firstDeleted U Y m n ω = some a → μ.survivor U Y m n ω = some a :=
  restrictOutput_some_original _ _

theorem firstDeleted_some_original (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (ω : Ω) (a : A) :
    μ.firstDeleted U Y m n ω = some a → U ω = some a := fun h =>
  μ.survivor_some_original U Y m n ω a (μ.firstDeleted_some_survivor U Y m n ω a h)

theorem ancestor_mass_partition (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) :
    μ.prob (fun ω => μ.survivor U Y m n ω ≠ none) +
      ∑ j ∈ Finset.range n, μ.prob (fun ω => μ.firstDeleted U Y m j ω ≠ none) =
        μ.prob (fun ω => U ω ≠ none) := by
  induction n with
  | zero => simp [survivor]
  | succ n ih =>
    have h := μ.kept_deleted_mass (μ.survivor U Y m n) (Y n) m
    change μ.prob (fun ω => μ.survivor U Y m (n+1) ω ≠ none) +
      μ.prob (fun ω => μ.firstDeleted U Y m n ω ≠ none) = _ at h
    rw [Finset.sum_range_succ]
    linarith

def budgetPart (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m n : ℕ) :
    Option (Fin n) → Ω → Option A
  | none => μ.survivor U Y m (n+1)
  | some i => μ.firstDeleted U Y m (i.val+1)

def budgetView (Y : ℕ → Ω → B) (n : ℕ) : Option (Fin n) → Ω → B
  | none => Y n
  | some i => Y i.val

theorem budgetPart_mass (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m n : ℕ) :
    (∑ i, μ.prob (fun ω => μ.budgetPart U Y m n i ω ≠ none)) +
      μ.prob (fun ω => μ.firstDeleted U Y m 0 ω ≠ none) = μ.prob (fun ω => U ω ≠ none) := by
  have h := μ.ancestor_mass_partition U Y m (n+1)
  rw [Finset.sum_range_succ'] at h
  simp only [budgetPart, Fintype.sum_option,
    Fin.sum_univ_eq_sum_range (fun i => μ.prob (fun ω => μ.firstDeleted U Y m (i+1) ω ≠ none)) n]
  linarith

theorem budgetPart_mass_le (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m n : ℕ) :
    (∑ i, μ.prob (fun ω => μ.budgetPart U Y m n i ω ≠ none)) ≤ μ.prob (fun ω => U ω ≠ none) := by
  have h := μ.budgetPart_mass U Y m n
  linarith [μ.prob_nonneg (fun ω => μ.firstDeleted U Y m 0 ω ≠ none)]

theorem budgetPart_some_original (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (i : Option (Fin n)) (ω : Ω) (a : A) :
    μ.budgetPart U Y m n i ω = some a → U ω = some a := by
  cases i with
  | none => exact μ.survivor_some_original U Y m (n+1) ω a
  | some i => exact μ.firstDeleted_some_original U Y m (i.val+1) ω a

theorem survivor_short_support (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (b : B) (hb : 0 < (μ.map (Y n)).weight b) (a : A)
    (ha : a ∉ ((μ.given (Y n) b).map (μ.survivor U Y m n)).outputList m) :
    ((μ.given (Y n) b).map (μ.survivor U Y m (n+1))).weight (some a) = 0 :=
  μ.kept_given_support (μ.survivor U Y m n) (Y n) m b hb a ha

theorem firstDeleted_short_support (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (b : B) (hb : 0 < (μ.map (Y n)).weight b) (a : A)
    (ha : a ∉ ((μ.given (Y n) b).map (μ.survivor U Y m n)).outputList m) :
    ((μ.given (Y n) b).map (μ.firstDeleted U Y m (n+1))).weight (some a) = 0 := by
  apply le_antisymm _ (((μ.given (Y n) b).map _).nonneg _)
  calc
    _ ≤ ((μ.given (Y n) b).map (μ.survivor U Y m (n+1))).weight (some a) :=
      (μ.given (Y n) b).prob_mono (fun ω h =>
        μ.firstDeleted_some_survivor U Y m (n+1) ω a h)
    _ = 0 := μ.survivor_short_support U Y m n b hb a ha

omit [Fintype C] in
theorem budgetPart_zero_conflict (μ : FiniteProb Ω) (U V : Ω → Option A)
    (Y Z : ℕ → Ω → B) (m n : ℕ) (F : Ω → C) (E : C → A → A → Prop)
    (hz : μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) = 0) (i : Option (Fin n)) :
    μ.prob (fun ω => selectedConflict E
      (F ω,μ.budgetPart U Y m n i ω,μ.budgetPart V Z m n i ω)) = 0 := by
  apply le_antisymm _ (μ.prob_nonneg _)
  calc
    _ ≤ μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) := μ.prob_mono (fun ω =>
      selectedConflict_of_restriction E _ _ _ _ _
        (μ.budgetPart_some_original U Y m n i ω) (μ.budgetPart_some_original V Z m n i ω))
    _ = 0 := hz

end FiniteProb
end
end MISLocal
