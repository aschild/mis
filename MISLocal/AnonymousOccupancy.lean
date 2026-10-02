import MISLocal.AnonymousTransport

/-! The occupancy bound with ordinary anonymity built into the algorithm
interface. There is no separately supplied locality or symmetry certificate. -/

open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every anonymous `(n+1)`-round rule on a finite regular graph with tree
edge neighborhoods and independent fair matrices satisfies the occupancy
bound. Private values are iid with any common finite distribution `R`. -/
theorem anonymous_graph_occupancy {d n k : ℕ}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    {Q : Type} [Fintype Q] (R : FiniteProb Q)
    (A : AnonymousRule V G.edgeSet k Q) (e₀ : G.edgeSet)
    (hzero : (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),runAnonymous G A (n+1) (edgeLeft G e₀) ω,
          runAnonymous G A (n+1) (edgeRight G e₀) ω)) = 0)
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob
      (fun ω => runAnonymous G A (n+1) (edgeLeft G e₀) ω ≠ none) ≤
        occupancyCap (n+1) ((d+1:ℕ):ℝ) :=
  graph_occupancy G hreg ht (fun _ => R) (runAnonymous G A (n+1))
    (runAnonymous_local G A (n+1)) (anonymous_homogeneous G hreg ht R A)
    e₀ hzero hD hk hlower hupper

end TreeGeometry
end
end MISLocal
