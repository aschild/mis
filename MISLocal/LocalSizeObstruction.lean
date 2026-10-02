import MISLocal.ConcreteFiniteObstruction
import MISLocal.LocalGraphRealization
import MISLocal.SuccessObstruction
/-! Only the local clique ball needs to fit on the n-vertex legal input. -/
open MeasureTheory
open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry
variable {V Tape State : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (A : UniformLocalProtocol (2^b) Tape State) [MeasurableSpace Tape]
    (ν : Measure (Fin (2^b) → Tape)) [IsProbabilityMeasure ν] (T : ℕ)
theorem local_size_obstruction {d : ℕ} (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (T+3))).IsTree) (e : G.edgeSet)
    (hfit : (ballFinset G (T+2) (edgeLeft G e)).card*(2*m) ≤ 2^b)
    (ε : ℝ) (hε : ε ≤ 1)
    (hcorrect : ∀ K : SimpleGraph (Fin (2^b)), 1-ε ≤ ν.real {W | Maximal K.IsIndepSet (A.candidates K id W T)})
    (hmeas : ∀ (M : G.edgeSet → EdgeMatrix (2*m)) (z : V × Fin (2*m)),
      MeasurableSet {W | z ∈ A.candidates (cliqueBlowup G M) (extractedIdentifiers G pack M) W T})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ 2*m)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log ((2*m:ℕ):ℝ))
    (hupper : Real.log ((2*m:ℕ):ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (1-ε)*(1-localCollisionError G (m := m) (b := b) T (edgeLeft G e)-
      localDominationError (m := m) (d+1)) ≤ occupancyCap (T+3) ((d+1:ℕ):ℝ) := by
  let μ := FiniteProb.pi (matrixPrivateProbability G (2*m) (fun _ => FiniteProb.uniform Unit))
  let matrix := fun ω : ∀ i, matrixPrivateType G (2*m) (fun _ => Unit) i => fun e => ω (Sum.inl e)
  let root := edgeLeft G e
  let H := fun ω => cliqueBlowup G (matrix ω)
  let U : Set (V × Fin (2*m)) := {z | InBall G (T+2) root z.1}
  have hn : Fintype.card U ≤ 2^b := by
    calc
      Fintype.card U = Fintype.card {z : V × Fin (2*m) // InBall G (T+2) root z.1} := Fintype.card_congr (Equiv.refl _)
      _ = (ballFinset G (T+2) root).card*(2*m) := cliqueBall_card G root
      _ ≤ 2^b := hfit
  let ids := fun ω => extractedIdentifiers G pack (matrix ω)
  let K := fun ω => localRealization (H ω) U (ids ω) hn
  let S := fun ω W => snapshotCandidates pack A W T (fullEdgeSnapshot G (matrix ω) root)
  let unique := fun ω => locallyUniqueIDs G pack T root (matrix ω)
  apply success_obstruction μ ν unique (fun ω => ExternallyDominatable (H ω) (vertexClique root))
    (fun ω W => Maximal (K ω).IsIndepSet (A.candidates (K ω) id W T))
    (fun ω W => Occupies (vertexClique root) (repair (H ω) (S ω W))) ε
    (localCollisionError G (m := m) (b := b) T root) (localDominationError (m := m) (d+1)) _ hε
  · dsimp only [μ,unique,locallyUniqueIDs,matrix]
    rw [matrixUnitProbability_prob G (2*m)
      (fun M => ¬Set.InjOn (extractedIdentifiers G pack M) {z | InBall G (T+2) root z.1})]
    exact extracted_local_collision_bound G pack (by intro v; rw [hreg]; omega) (T+2) root
  · dsimp only [μ,H,matrix]
    rw [matrixUnitProbability_prob G (2*m) (fun M => ExternallyDominatable (cliqueBlowup G M) (vertexClique root))]
    have h := external_domination_probability G (k := 2*m) root
    rw [hreg root] at h
    exact h
  · exact fun ω => hcorrect (K ω)
  · intro ω hu hno W hc
    apply realization_forces_repaired_occupancy A (H ω) (vertexClique root) U (ids ω) hn W T (S ω W) hu hno _ hc
    intro v hv z hz
    have hvr : v.1 = root := hv
    have hzr : InBall G 1 root z.1 := by
      rcases hz with hz | hz
      · exact Or.inl ((congrArg Prod.fst hz).trans hvr)
      · rcases blowup_adj_skeleton G (matrix ω) hz with he | ha
        · exact Or.inl (he.symm.trans hvr)
        · exact Or.inr ⟨z.1,hvr ▸ ha,rfl⟩
    have hball (w : V × Fin (2*m)) (hw : InBall G (T+1) z.1 w.1) : w ∈ U := by
      simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using inBall_trans G hzr hw
    have hzu : z ∈ U := hball z (inBall_self G (T+1) z.1)
    refine ⟨hzu,fun w hw => hball w (blowup_ball_skeleton G (matrix ω) (T+1) z w hw),?_⟩
    have huniq : snapshotUnique pack T (fullEdgeSnapshot G (matrix ω) root) z.1 := by
      unfold snapshotUnique
      rw [fullSnapshotIdentifiers G pack (matrix ω) root,fullSnapshotSkeleton G (matrix ω) root]
      exact fun a ha b hb hab => hu (hball a ha) (hball b hb) hab
    simp only [S,snapshotCandidates,Set.mem_setOf_eq,huniq,true_and,
      fullSnapshotBlowup G (matrix ω) root,fullSnapshotIdentifiers G pack (matrix ω) root]
    rfl
  · intro ω
    apply repaired_occupancy_measurable (H ω) (vertexClique root) (S ω)
    intro z
    by_cases hu : snapshotUnique pack T (fullEdgeSnapshot G (matrix ω) root) z.1
    · have h := hmeas (matrix ω) z
      simpa only [S,snapshotCandidates,Set.mem_setOf_eq,hu,true_and,
        fullSnapshotBlowup G (matrix ω) root,fullSnapshotIdentifiers G pack (matrix ω) root] using h
    · simp only [S,snapshotCandidates,Set.mem_setOf_eq,hu,false_and]; exact MeasurableSet.empty
  · exact fun W => concrete_fixed_table_occupancy G pack A W T hreg ht e hD hk hlower hupper
end TreeGeometry
end
end MISLocal
