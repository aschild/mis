import MISLocal.UniformExtraction
import MISLocal.DirectedIdentifiers

/-! Fair bits stay jointly uniform under any injection of coordinate sets. -/

open scoped Classical
namespace MISLocal
noncomputable section

def bitVectorGroupEquiv (I : Type*) : (I → Bool) ≃ (I → ZMod 2) :=
  Equiv.piCongrRight (fun _ => bitGroupEquiv)

def coordinateRestriction {I J : Type*} (f : I ↪ J) : (J → ZMod 2) →+ (I → ZMod 2) where
  toFun x i := x (f i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coordinateRestriction_surjective {I J : Type*} (f : I ↪ J) :
    Function.Surjective (coordinateRestriction f) := by
  intro x
  refine ⟨Function.extend f x (fun _ => 0),?_⟩
  funext i
  exact f.injective.extend_apply x (fun _ => 0) i

namespace FiniteProb

theorem fairBits_map_restriction {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (f : I ↪ J) :
    (fairBits J).map (fun x => fun i => x (f i)) = fairBits I := by
  have hJ : fairBits J = uniform (J → Bool) := pi_uniform
  have hI : fairBits I = uniform (I → Bool) := pi_uniform
  rw [hJ,hI]
  calc
    _ = (((uniform (J → Bool)).map (bitVectorGroupEquiv J)).map
        (coordinateRestriction f)).map (bitVectorGroupEquiv I).symm := by
      rw [map_comp,map_comp]
      congr 1
      funext x i
      exact (bitGroupEquiv.symm_apply_apply (x (f i))).symm
    _ = _ := by
      rw [uniform_map_equiv,uniform_map_surjective_addHom _ (coordinateRestriction_surjective f),
        uniform_map_equiv]

end FiniteProb
end
end MISLocal
