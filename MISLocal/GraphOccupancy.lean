import MISLocal.FiniteOccupancy
import MISLocal.GraphInputGeometry
import MISLocal.PrivateGeometry

/-! The concrete graph occupancy theorem. Inputs are independent fair
Boolean matrices on actual edges, together with independent finite private
randomness at each vertex. The round views and their geometric properties
are constructed from the graph, rather than supplied as a certificate.

Symmetry is the explicit input/output relabeling condition `ViewHomogeneous`.
There are no assumed entropy, support, truncation, or occupancy estimates.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

namespace FiniteProb

theorem pi_map_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] (P : ∀ i, FiniteProb (T i)) (i : I) :
    (pi P).map (fun x => x i) = P i := by
  ext a
  change (pi P).expect (fun x => bit (x i = a)) = _
  rw [pi_expect_coordinate P i (fun b => bit (b=a))]
  simp [expect, bit]

end FiniteProb

namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev matrixPrivateType (k : ℕ) (Q : V → Type) : G.edgeSet ⊕ V → Type :=
  Sum.elim (fun _ => Fin k × Fin k → Bool) Q

def matrixPrivateProbability (k : ℕ) {Q : V → Type} [∀ v, Fintype (Q v)]
    (R : ∀ v, FiniteProb (Q v)) :
    ∀ i, FiniteProb (matrixPrivateType G k Q i) :=
  FiniteProb.sumProb (fun _ => FiniteProb.fairBits (Fin k × Fin k)) R

/-- Occupancy of an `(n+1)`-round homogeneous independent-set rule, with
private vertex randomness. The local-tree hypothesis refers to finite
neighborhoods only: the whole regular graph is not assumed to be a tree. -/
theorem graph_occupancy {d n k : ℕ}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    {Q : V → Type} [∀ v, Fintype (Q v)] (R : ∀ v, FiniteProb (Q v))
    (U : V → (∀ i, matrixPrivateType G k Q i) → Option (Fin k))
    (hlocal : ∀ v, ReadsOnly (U v) (privateReads (seen G (n+1)) v))
    (hhom : ViewHomogeneous (FiniteProb.pi (matrixPrivateProbability G k R)) U
      (fun j v => observeInputs (rawView (V := V) (seen G (n+1-j) v)))
      (fun j e => observeInputs (rawView (V := V) (sharedEdges G (n+1-j) e)))
      (edgeLeft G) (edgeRight G))
    (e₀ : G.edgeSet)
    (hzero : (FiniteProb.pi (matrixPrivateProbability G k R)).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),U (edgeLeft G e₀) ω,U (edgeRight G e₀) ω)) = 0)
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G k R)).prob
      (fun ω => U (edgeLeft G e₀) ω ≠ none) ≤ occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  let g := (graphInputGeometry G d n hreg ht).withPrivate
  let P := matrixPrivateProbability G k R
  let decode := fun (_ : ℕ) (y : ∀ i, Option (matrixPrivateType G k Q i)) =>
    (y (Sum.inl e₀)).getD (fun _ => false)
  have hd (j : ℕ) (_ : j ≤ n+1) (ω : ∀ i, matrixPrivateType G k Q i) :
      decode j (g.sharedObservation j e₀ ω) = ω (Sum.inl e₀) := by
    have he : e₀ ∈ sharedEdges G (n+1-j) e₀ := Finset.mem_insert_self _ _
    simp only [decode, g, ProductInputGeometry.sharedObservation,
      ProductInputGeometry.withPrivate, graphInputGeometry, observeInputs,
      rawView, Finset.mem_map, Function.Embedding.inl_apply, Sum.inl.injEq,
      exists_eq_right, he, if_true, Option.getD_some]
  exact FiniteProb.finite_occupancy P g U hlocal hhom e₀ (fun ω => ω (Sum.inl e₀))
    decode hd (FiniteProb.pi_map_coordinate P (Sum.inl e₀)) hzero hD hk hlower hupper

end TreeGeometry
end
end MISLocal
