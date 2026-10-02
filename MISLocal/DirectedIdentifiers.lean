import MISLocal.CliqueBlowup
import MISLocal.UniformExtraction

/-! An actual extractor on the fair edge matrices. The two orientations use
disjoint off-diagonal blocks. All outgoing blocks at a vertex are added, so
the extractor does not choose or order an incident edge. A chosen incident
edge occurs only in the surjectivity proof. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

def lowerHalf (m : ℕ) (i : Fin m) : Fin (2*m) := ⟨i.val,by omega⟩
def upperHalf (m : ℕ) (i : Fin m) : Fin (2*m) := ⟨m+i.val,by omega⟩

def directedBlockPosition (m : ℕ) (z : Bool × (Fin m × Fin m)) :
    Fin (2*m) × Fin (2*m) :=
  if z.1 then (upperHalf m z.2.2,lowerHalf m z.2.1)
    else (lowerHalf m z.2.1,upperHalf m z.2.2)

theorem directedBlockPosition_injective (m : ℕ) :
    Function.Injective (directedBlockPosition m) := by
  rintro ⟨b,p⟩ ⟨c,q⟩ h
  cases b <;> cases c
  · have h₁ := congrArg (fun x => x.1.val) h
    have h₂ := congrArg (fun x => x.2.val) h
    simp only [directedBlockPosition,Bool.false_eq_true,if_false,lowerHalf,upperHalf,Prod.fst,Prod.snd] at h₁ h₂
    exact Prod.ext rfl (Prod.ext (Fin.ext h₁) (Fin.ext (Nat.add_left_cancel h₂)))
  · have h₁ := congrArg (fun x => x.1.val) h
    simp only [directedBlockPosition,Bool.false_eq_true,if_false,if_true,lowerHalf,upperHalf,Prod.fst,Prod.snd] at h₁
    have hp := p.1.isLt
    omega
  · have h₁ := congrArg (fun x => x.1.val) h
    simp only [directedBlockPosition,Bool.false_eq_true,if_false,if_true,lowerHalf,upperHalf,Prod.fst,Prod.snd] at h₁
    have hq := q.1.isLt
    omega
  · have h₁ := congrArg (fun x => x.1.val) h
    have h₂ := congrArg (fun x => x.2.val) h
    simp only [directedBlockPosition,if_true,lowerHalf,upperHalf,Prod.fst,Prod.snd] at h₁ h₂
    exact Prod.ext rfl (Prod.ext (Fin.ext h₂) (Fin.ext (Nat.add_left_cancel h₁)))

def blockRestriction {E : Type*} (m : ℕ) :
    (E → Fin (2*m) × Fin (2*m) → ZMod 2) →+
      ((E × Bool) → Fin m × Fin m → ZMod 2) where
  toFun x eb p := x eb.1 (directedBlockPosition m (eb.2,p))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem blockRestriction_surjective {E : Type*} (m : ℕ) :
    Function.Surjective (blockRestriction (E := E) m) := by
  intro y
  refine ⟨fun e => Function.extend (directedBlockPosition m)
    (fun bp => y (e,bp.1) bp.2) (fun _ => 0),?_⟩
  funext eb p
  change Function.extend (directedBlockPosition m)
    (fun bp => y (eb.1,bp.1) bp.2) (fun _ => 0)
      (directedBlockPosition m (eb.2,p)) = _
  exact (directedBlockPosition_injective m).extend_apply _ _ (eb.2,p)

/-- Add all source strings having the indicated endpoint. -/
def endpointSum {J V A : Type*} [Fintype J] [AddCommGroup A]
    (endpoint : J → V) : (J → A) →+ (V → A) where
  toFun x v := ∑ j, if endpoint j = v then x j else 0
  map_zero' := by ext v; simp
  map_add' := by
    intro x y; ext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : endpoint j = v <;> simp [h]

theorem endpointSum_surjective {J V A : Type*} [Fintype J] [AddCommGroup A]
    (endpoint : J → V) (h : Function.Surjective endpoint) :
    Function.Surjective (endpointSum (A := A) endpoint) := by
  let chooseSource : V → J := fun v => (h v).choose
  have hs (v : V) : endpoint (chooseSource v) = v := (h v).choose_spec
  intro y
  refine ⟨fun j => if j = chooseSource (endpoint j) then y (endpoint j) else 0,?_⟩
  funext v
  change (∑ j, if endpoint j = v then
    (if j = chooseSource (endpoint j) then y (endpoint j) else 0) else 0) = y v
  rw [Finset.sum_eq_single (chooseSource v)]
  · simp [hs]
  · intro j _ hj
    by_cases he : endpoint j = v
    · simp [he,hj]
    · simp [he]
  · simp

def bitGroupEquiv : Bool ≃ ZMod 2 :=
  Fintype.equivOfCardEq (by simp [ZMod.card])

def matrixBitGroupEquiv {E : Type*} (m : ℕ) :
    (E → EdgeMatrix (2*m)) ≃ (E → Fin (2*m) × Fin (2*m) → ZMod 2) where
  toFun x e p := bitGroupEquiv (x e p)
  invFun x e p := bitGroupEquiv.symm (x e p)
  left_inv x := by ext e p; exact bitGroupEquiv.symm_apply_apply _
  right_inv x := by ext e p; exact bitGroupEquiv.apply_symm_apply _

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

def outgoingEndpoint (eb : G.edgeSet × Bool) : V :=
  if eb.2 then edgeRight G eb.1 else edgeLeft G eb.1

theorem outgoingEndpoint_surjective (hdegree : ∀ v, 0 < G.degree v) :
    Function.Surjective (outgoingEndpoint G) := by
  intro v
  have hc : 0 < (Finset.univ.filter
      (edgeIncident (edgeLeft G) (edgeRight G) v)).card := by
    rw [incident_card_eq_degree G v]; exact hdegree v
  obtain ⟨e,he⟩ := Finset.card_pos.mp hc
  rcases (Finset.mem_filter.mp he).2 with hl | hr
  · exact ⟨(e,false),hl⟩
  · exact ⟨(e,true),hr⟩

def vertexBlockSum (m : ℕ) :
    (G.edgeSet → Fin (2*m) × Fin (2*m) → ZMod 2) →+
      (V → Fin m × Fin m → ZMod 2) :=
  (endpointSum (A := Fin m × Fin m → ZMod 2) (outgoingEndpoint G)).comp
    (blockRestriction m)

def extractedBlockStrings (m : ℕ) (M : G.edgeSet → EdgeMatrix (2*m)) :
    V → Fin m × Fin m → ZMod 2 :=
  vertexBlockSum G m (matrixBitGroupEquiv m M)

theorem extractedBlockStrings_jointly_uniform (m : ℕ)
    (hdegree : ∀ v, 0 < G.degree v) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))).map
      (extractedBlockStrings G m) = FiniteProb.uniform (V → Fin m × Fin m → ZMod 2) := by
  have hb : FiniteProb.fairBits (Fin (2*m) × Fin (2*m)) =
      FiniteProb.uniform (EdgeMatrix (2*m)) := FiniteProb.pi_uniform
  rw [hb,FiniteProb.pi_uniform]
  change (FiniteProb.uniform (G.edgeSet → EdgeMatrix (2*m))).map
    (fun M => vertexBlockSum G m (matrixBitGroupEquiv m M)) = _
  rw [← FiniteProb.map_comp,FiniteProb.uniform_map_equiv]
  apply FiniteProb.uniform_map_surjective_addHom
  exact (endpointSum_surjective (outgoingEndpoint G) (outgoingEndpoint_surjective G hdegree)).comp
    (blockRestriction_surjective m)

end TreeGeometry
end
end MISLocal
