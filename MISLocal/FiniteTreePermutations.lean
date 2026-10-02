import MISLocal.PrefixTree
import Mathlib.GroupTheory.Perm.Basic
/-! Finite involutions agreeing with the colored regular tree inside a word ball. -/
open scoped Classical
namespace MISLocal
noncomputable section
namespace FiniteTree
variable {α : Type*} [DecidableEq α]
def Reduced : List α → Prop
  | [] => True
  | [_] => True
  | i::j::w => i ≠ j ∧ Reduced (j::w)
omit [DecidableEq α] in
theorem reduced_tail {i : α} {w : List α} (h : Reduced (i::w)) : Reduced w := by
  cases w with
  | nil => trivial
  | cons j w => exact h.2
def rawToggle (i : α) : List α → List α
  | [] => [i]
  | j::w => if j = i then w else i::j::w
theorem rawToggle_reduced (i : α) {w : List α} (h : Reduced w) : Reduced (rawToggle i w) := by
  cases w with
  | nil => trivial
  | cons j w =>
    by_cases hj : j = i
    · simpa only [rawToggle,if_pos hj] using reduced_tail h
    · simpa only [rawToggle,if_neg hj,Reduced] using And.intro (Ne.symm hj) h
theorem rawToggle_involutive (i : α) {w : List α} (h : Reduced w) : rawToggle i (rawToggle i w) = w := by
  cases w with
  | nil => simp [rawToggle]
  | cons j w =>
    by_cases hj : j = i
    · subst j
      cases w with
      | nil => simp [rawToggle]
      | cons j w =>
        have hj : j ≠ i := Ne.symm h.1
        simp [rawToggle,hj]
    · simp [rawToggle,hj]
theorem rawToggle_length (i : α) (w : List α) : (rawToggle i w).length ≤ w.length+1 := by
  cases w <;> simp only [rawToggle,List.length_nil,List.length_cons]
  · omega
  · split
    · omega
    · simp only [List.length_cons]
      omega
def Word (α : Type*) (L : ℕ) := {w : List α // Reduced w ∧ w.length ≤ L}
instance [Finite α] (L : ℕ) : Finite (Word α L) :=
  Set.Finite.to_subtype ((List.finite_length_le α L).subset (fun _ h => h.2))
instance [Fintype α] (L : ℕ) : Fintype (Word α L) := Fintype.ofFinite _
def emptyWord (L : ℕ) : Word α L := ⟨[],by simp [Reduced]⟩
def toggle (L : ℕ) (i : α) (w : Word α L) : Word α L :=
  if h : (rawToggle i w.val).length ≤ L then
    ⟨rawToggle i w.val,rawToggle_reduced i w.property.1,h⟩ else w
theorem toggle_involutive (L : ℕ) (i : α) : Function.Involutive (toggle L i) := by
  intro w
  by_cases h : (rawToggle i w.val).length ≤ L
  · have he := rawToggle_involutive i w.property.1
    have hh : (rawToggle i (rawToggle i w.val)).length ≤ L := by rw [he]; exact w.property.2
    apply Subtype.ext
    simp only [toggle,dif_pos h,dif_pos hh]
    exact he
  · simp only [toggle,dif_neg h]
def generator (L : ℕ) (i : α) : Equiv.Perm (Word α L) :=
  ⟨toggle L i,toggle L i,toggle_involutive L i,toggle_involutive L i⟩
theorem generator_sq (L : ℕ) (i : α) : generator L i * generator L i = 1 := by
  ext w
  exact toggle_involutive L i w
theorem generator_val {L : ℕ} (i : α) (w : Word α L) (h : w.val.length < L) :
    (generator L i w).val = rawToggle i w.val := by
  have hb : (rawToggle i w.val).length ≤ L := le_trans (rawToggle_length i _) (by omega)
  simp only [generator,Equiv.coe_fn_mk,toggle,dif_pos hb]
theorem generator_empty {L : ℕ} (hL : 1 ≤ L) (i : α) :
    (generator L i (emptyWord L)).val = [i] :=
  generator_val i (emptyWord L) (by simpa only [emptyWord,List.length_nil] using hL)
def product (L : ℕ) : List α → Equiv.Perm (Word α L)
  | [] => 1
  | i::w => generator L i * product L w
theorem product_toggle (L : ℕ) (i : α) {w : List α} (h : Reduced w) :
    product L (rawToggle i w) = generator L i * product L w := by
  cases w with
  | nil => simp [rawToggle,product]
  | cons j w =>
    by_cases hj : j = i
    · subst j
      simp [rawToggle,product,← mul_assoc,generator_sq]
    · simp only [rawToggle,if_neg hj,product]
theorem product_eval (L : ℕ) {w : List α} (h : Reduced w) (hL : w.length ≤ L) :
    (product L w (emptyWord L)).val = w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hwL : w.length < L := by simpa only [List.length_cons] using hL
    have hw := ih (reduced_tail h) (Nat.le_of_lt hwL)
    change (generator L i (product L w (emptyWord L))).val = i::w
    rw [generator_val i _ (by rw [hw]; exact hwL),hw]
    cases w with
    | nil => rfl
    | cons j w => simp only [rawToggle,if_neg (Ne.symm h.1)]
theorem product_eval_injective (L : ℕ) : Function.Injective (fun w : Word α L => product L w.val) := by
  intro w z h
  have he := congrArg (fun p : Equiv.Perm (Word α L) => (p (emptyWord L)).val) h
  dsimp only at he
  rw [product_eval L w.property.1 w.property.2,product_eval L z.property.1 z.property.2] at he
  exact Subtype.ext he
end FiniteTree
end
end MISLocal
