import MISLocal.Extraction
import MISLocal.ProductSources
import Mathlib.Data.ZMod.Basic

/-! Exact uniformity, including the whole extracted vector. A surjective
additive map between finite groups sends uniform input to uniform output.
No pairwise-independence shortcut is used in this step. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section
namespace FiniteProb

theorem uniform_map_equiv {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    [Nonempty B] (e : A ≃ B) : (uniform A).map e = uniform B := by
  ext b
  rw [map_equiv_weight]
  simp only [uniform,Fintype.card_congr e]

theorem pi_uniform {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    pi (fun i => uniform (A i)) = uniform (∀ i, A i) := by
  ext x
  simp only [pi,uniform,Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

def additiveFiberSplit {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Surjective f) :
    A ≃ B × {a : A // f a = 0} where
  toFun a := (f a,⟨a-(hf (f a)).choose,by simp [(hf (f a)).choose_spec]⟩)
  invFun z := (hf z.1).choose + z.2.val
  left_inv a := by simp
  right_inv z := by
    apply Prod.ext
    · simp [(hf z.1).choose_spec,z.2.property]
    · apply Subtype.ext
      simp [(hf z.1).choose_spec,z.2.property]

theorem uniform_map_surjective_addHom {A B : Type*}
    [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Surjective f) :
    (uniform A).map f = uniform B := by
  ext b
  letI : Nonempty {a : A // f a = 0} := ⟨⟨0,map_zero f⟩⟩
  change (uniform A).prob (fun a => f a = b) = _
  simpa only [additiveFiberSplit,uniform,one_div] using
    uniform_first_coordinate (additiveFiberSplit f hf) b

end FiniteProb
end
end MISLocal
