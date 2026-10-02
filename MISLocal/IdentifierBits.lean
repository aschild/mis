import MISLocal.DirectedIdentifiers
import MISLocal.Collisions

/-! Convert disjoint pieces of each uniform vertex string into legal-range
tentative IDs. On the power-of-two size sequence no modulo bias is needed. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

def wordIdentifierEquiv (b : ℕ) : (Fin b → ZMod 2) ≃ Fin (2^b) :=
  Fintype.equivOfCardEq (by simp [ZMod.card])

def readIdentifierBits {V : Type*} {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m)) :
    (V → Fin m × Fin m → ZMod 2) →+ ((V × Fin (2*m)) → Fin b → ZMod 2) where
  toFun x va t := x va.1 (pack (va.2,t))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem readIdentifierBits_surjective {V : Type*} {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m)) :
    Function.Surjective (readIdentifierBits (V := V) pack) := by
  intro y
  refine ⟨fun v => Function.extend pack (fun pair => y (v,pair.1) pair.2) (fun _ => 0),?_⟩
  funext va t
  change Function.extend pack (fun pair => y (va.1,pair.1) pair.2) (fun _ => 0) (pack (va.2,t)) = _
  exact pack.injective.extend_apply _ _ _

def wordsIdentifierEquiv {X : Type*} (b : ℕ) :
    (X → Fin b → ZMod 2) ≃ (X → Fin (2^b)) :=
  Equiv.piCongrRight (fun _ => wordIdentifierEquiv b)

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m b : ℕ} (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))

def extractedIdentifiers (M : G.edgeSet → EdgeMatrix (2*m)) :
    (V × Fin (2*m)) → Fin (2^b) :=
  wordsIdentifierEquiv b (readIdentifierBits pack (extractedBlockStrings G m M))

theorem extractedIdentifiers_jointly_uniform (hdegree : ∀ v, 0 < G.degree v) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))).map
      (extractedIdentifiers G pack) = FiniteProb.uniform ((V × Fin (2*m)) → Fin (2^b)) := by
  let μ := FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))
  calc
    μ.map (extractedIdentifiers G pack) =
        ((μ.map (extractedBlockStrings G m)).map (readIdentifierBits pack)).map
          (wordsIdentifierEquiv b) := by rw [FiniteProb.map_comp,FiniteProb.map_comp]; rfl
    _ = _ := by
      rw [extractedBlockStrings_jointly_uniform G m hdegree,
        FiniteProb.uniform_map_surjective_addHom _ (readIdentifierBits_surjective pack),
        FiniteProb.uniform_map_equiv]

end TreeGeometry
end
end MISLocal
