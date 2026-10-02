import MISLocal.GraphOccupancy
import MISLocal.GraphViewTransport
import MISLocal.InputRelabeling

/-! An anonymous rule is one function on rooted, matrix-labeled views
modulo renaming vertices and edges. Vertex names are not algorithm inputs.
Private randomness uses the same finite alphabet and distribution at every
vertex; a sampled value can distinguish a root, but a skeleton name cannot. -/

open scoped Classical
namespace MISLocal
noncomputable section

abbrev EdgeMatrix (k : ℕ) := Fin k × Fin k → Bool

def transposeMatrix {k : ℕ} (M : EdgeMatrix k) : EdgeMatrix k := fun p => M p.swap

def matrixFlip (k : ℕ) (b : Bool) : EdgeMatrix k ≃ EdgeMatrix k where
  toFun M := if b then transposeMatrix M else M
  invFun M := if b then transposeMatrix M else M
  left_inv M := by cases b <;> rfl
  right_inv M := by cases b <;> rfl

structure NamedLocalView (V E : Type*) (k : ℕ) (Q : Type*) where
  root : V
  coin : Q
  edges : E → Option (V × V × EdgeMatrix k)

def renameEdgeDatum {V : Type*} {k : ℕ} (φ : V ≃ V) (b : Bool)
    (z : V × V × EdgeMatrix k) : V × V × EdgeMatrix k :=
  if b then (φ z.2.1,φ z.1,transposeMatrix z.2.2) else (φ z.1,φ z.2.1,z.2.2)

/-- Renaming changes only vertex/edge names and the arbitrary orientation
used to store an undirected edge matrix. It preserves all observed values. -/
def LocalViewRenaming {V E : Type*} {k : ℕ} {Q : Type*}
    (x y : NamedLocalView V E k Q) : Prop :=
  ∃ (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool),
    y.root = φ x.root ∧ y.coin = x.coin ∧
    ∀ i, y.edges (ψ i) = (x.edges i).map (renameEdgeDatum φ (flip i))

/-- `Quot` identifies every renaming above (and its equivalence closure).
There is no equivariance or probabilistic hypothesis in this definition. -/
abbrev AnonymousLocalView (V E : Type*) (k : ℕ) (Q : Type*) :=
  Quot (@LocalViewRenaming V E k Q)

abbrev AnonymousRule (V E : Type*) (k : ℕ) (Q : Type*) :=
  AnonymousLocalView V E k Q → Option (Fin k)

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {Q : Type}

def namedLocalView (r : ℕ) (v : V) (ω : ∀ i, matrixPrivateType G k (fun _ => Q) i) :
    NamedLocalView V G.edgeSet k Q where
  root := v
  coin := ω (Sum.inr v)
  edges i := if i ∈ seen G r v then some (edgeLeft G i,edgeRight G i,ω (Sum.inl i)) else none

def runAnonymous (A : AnonymousRule V G.edgeSet k Q) (r : ℕ)
    (v : V) (ω : ∀ i, matrixPrivateType G k (fun _ => Q) i) : Option (Fin k) :=
  A (Quot.mk _ (namedLocalView G r v ω))

theorem runAnonymous_local (A : AnonymousRule V G.edgeSet k Q) (r : ℕ) (v : V) :
    ReadsOnly (runAnonymous G A r v) (privateReads (seen G r) v) := by
  intro x y h
  have hc : x (Sum.inr v) = y (Sum.inr v) := h _ (by simp [privateReads])
  have he : (namedLocalView G r v x).edges = (namedLocalView G r v y).edges := by
    funext i
    by_cases hi : i ∈ seen G r v
    · have hxy := h (Sum.inl i) (by simp [privateReads, rawView, hi])
      simp only [namedLocalView, hi, if_true, hxy]
    · simp only [namedLocalView, hi, if_false]
  have hv : namedLocalView G r v x = namedLocalView G r v y := by
    exact congrArg₂ (fun coin edges => (⟨v,coin,edges⟩ : NamedLocalView V G.edgeSet k Q)) hc he
  exact congrArg (fun z => A (Quot.mk _ z)) hv

/-- Even on a graph with no automorphism sending `v` to `w`, a zero-round
anonymous rule cannot tell their skeleton names apart. Equal sampled private
values give equal outputs. -/
theorem runAnonymous_zero_same_coin (A : AnonymousRule V G.edgeSet k Q) (v w : V)
    (x y : ∀ i, matrixPrivateType G k (fun _ => Q) i)
    (hc : x (Sum.inr v) = y (Sum.inr w)) :
    runAnonymous G A 0 v x = runAnonymous G A 0 w y := by
  apply congrArg A
  apply Quot.sound
  refine ⟨Equiv.swap v w,Equiv.refl _,fun _ => false,?_,hc.symm,?_⟩
  · simp [namedLocalView]
  · intro i; simp [namedLocalView, seen]

end TreeGeometry
end
end MISLocal
