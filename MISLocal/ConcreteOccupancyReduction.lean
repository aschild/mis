import MISLocal.SnapshotLocality
import MISLocal.AnonymousTapeReduction
import MISLocal.ExtractedCollisions

/-! Invoke the occupancy theorem on the constructed LOCAL simulation.
Neither anonymity nor zero conflict nor radius is supplied as a hypothesis. -/

open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    {Tape State : Type*} (A : UniformLocalProtocol (2^b) Tape State)
    (W : Fin (2^b) → Tape) (T : ℕ)

theorem localAnonymousRule_noConflict (e : G.edgeSet)
    (ω : ∀ i, matrixPrivateType G (2*m) (fun _ => Unit) i) :
    ¬selectedConflict (fun M a b => M (a,b)=true)
      (ω (Sum.inl e),runAnonymous G (localAnonymousRule pack A W T) (T+3) (edgeLeft G e) ω,
        runAnonymous G (localAnonymousRule pack A W T) (T+3) (edgeRight G e) ω) := by
  rw [localAnonymousRule_representation G pack A W T ω (edgeLeft G e),
    localAnonymousRule_representation G pack A W T ω (edgeRight G e),
    snapshotCandidates_root_irrelevant G pack A W T _ (edgeRight G e) (edgeLeft G e)]
  exact repairedLabel_noConflict G _ _ e

variable [Nonempty V]

theorem concrete_fixed_table_occupancy {d : ℕ}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (T+3))).IsTree) (e : G.edgeSet)
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ 2*m)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log ((2*m:ℕ):ℝ))
    (hupper : Real.log ((2*m:ℕ):ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G (2*m) (fun _ => FiniteProb.uniform Unit))).prob
      (fun ω => Occupies (vertexClique (edgeLeft G e))
        (repair (cliqueBlowup G (fun i => ω (Sum.inl i)))
          (snapshotCandidates pack A W T
            (fullEdgeSnapshot G (fun i => ω (Sum.inl i)) (edgeLeft G e))))) ≤
      occupancyCap (T+3) ((d+1:ℕ):ℝ) := by
  have hz : (FiniteProb.pi (matrixPrivateProbability G (2*m) (fun _ => FiniteProb.uniform Unit))).prob
      (fun ω => selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e),runAnonymous G (localAnonymousRule pack A W T) (T+3) (edgeLeft G e) ω,
          runAnonymous G (localAnonymousRule pack A W T) (T+3) (edgeRight G e) ω)) = 0 := by
    simp only [FiniteProb.prob,FiniteProb.expect,bit,
      if_neg (localAnonymousRule_noConflict G pack A W T e _),mul_zero,Finset.sum_const_zero]
  have h := anonymous_graph_occupancy G (n := T+2) hreg ht (FiniteProb.uniform Unit)
    (localAnonymousRule pack A W T) e hz hD hk hlower hupper
  rw [FiniteProb.prob_congr _ (fun ω => by
    rw [localAnonymousRule_representation G pack A W T ω (edgeLeft G e),
      repairedLabel_occupies G])] at h
  exact h

end TreeGeometry
end
end MISLocal
