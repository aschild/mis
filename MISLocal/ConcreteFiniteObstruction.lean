import MISLocal.ConcreteOccupancyReduction
import MISLocal.BlowupIDCompletion
import MISLocal.MatrixUnitProbability
import MISLocal.CliqueDomination

/-! A concrete finite LOCAL obstruction. The collision and domination errors,
simulation, repaired representation, and per-fixed-table occupancy estimate
are all discharged. Correctness and measurability describe the supplied
randomized LOCAL program, rather than the desired lower bound. -/

open MeasureTheory
open scoped Classical
namespace MISLocal
noncomputable section

theorem repaired_occupancy_measurable {X W : Type*} [Fintype X] [MeasurableSpace W]
    (G : SimpleGraph X) (C : Set X) (S : W → Set X)
    (hS : ∀ x, MeasurableSet {w | x ∈ S w}) :
    MeasurableSet {w | Occupies C (repair G (S w))} := by
  have hr (x : X) : MeasurableSet {w | x ∈ repair G (S w)} := by
    apply (hS x).inter
    have hn (y : X) : MeasurableSet {w | G.Adj x y → y ∉ S w} := by
      by_cases hxy : G.Adj x y
      · simpa only [hxy,true_implies] using (hS y).compl
      · simp only [hxy,false_implies]
        exact MeasurableSet.univ
    simpa only [Set.iInter_setOf] using MeasurableSet.iInter hn
  change MeasurableSet {w | ∃ x, x ∈ C ∧ x ∈ repair G (S w)}
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ C
  · simpa only [hx,true_and] using hr x
  · simp only [hx,false_and]
    exact MeasurableSet.empty

namespace TreeGeometry
variable {V Tape State : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (enumeration : (V × Fin (2*m)) ≃ Fin (2^b))
    (A : UniformLocalProtocol (2^b) Tape State) [MeasurableSpace Tape]
    (ν : Measure (Fin (2^b) → Tape)) [IsProbabilityMeasure ν] (T : ℕ)

def localCollisionError (v : V) : ℝ :=
  (((ballFinset G (T+2) v).card*(2*m) : ℕ):ℝ) *
    ((((ballFinset G (T+2) v).card*(2*m) : ℕ):ℝ)-1) / ((2^b:ℕ):ℝ)

def localDominationError (D : ℕ) : ℝ :=
  ((2*m+1:ℕ):ℝ)^D * Real.exp (-((2*m:ℕ):ℝ)*(2:ℝ)^(-(D:ℤ)))

theorem concrete_finite_obstruction {d : ℕ}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (T+3))).IsTree) (e : G.edgeSet)
    (ε : ℝ) (hε : ε ≤ 1)
    (hcorrect : ∀ M : G.edgeSet → EdgeMatrix (2*m), 1-ε ≤ ν.real {W |
      Maximal (cliqueBlowup G M).IsIndepSet
        (A.candidates (cliqueBlowup G M)
          (completedBlowupIDs G pack enumeration T (edgeLeft G e) M) W T)})
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
  let S := fun ω W => snapshotCandidates pack A W T (fullEdgeSnapshot G (matrix ω) root)
  let out := fun ω W => A.candidates (H ω)
    (completedBlowupIDs G pack enumeration T root (matrix ω)) W T
  let unique := fun ω => locallyUniqueIDs G pack T root (matrix ω)
  apply finite_obstruction μ ν H (vertexClique root) out S unique ε
    (localCollisionError G (m := m) (b := b) T root)
    (localDominationError (m := m) (d+1)) _ hε
  · dsimp only [μ,unique,locallyUniqueIDs,matrix]
    rw [matrixUnitProbability_prob G (2*m)
      (fun M => ¬Set.InjOn (extractedIdentifiers G pack M) {z | InBall G (T+2) root z.1})]
    exact extracted_local_collision_bound G pack (by intro v; rw [hreg]; omega) (T+2) root
  · dsimp only [μ,H,matrix]
    rw [matrixUnitProbability_prob G (2*m)
      (fun M => ExternallyDominatable (cliqueBlowup G M) (vertexClique root))]
    have h := external_domination_probability G (k := 2*m) root
    rw [hreg root] at h
    exact h
  · exact fun ω => hcorrect (matrix ω)
  · intro ω hu W z hz w hw
    have hzroot : z.1 = root := hz
    have hb : InBall G 1 root w.1 := by
      rcases hw with hw | hw
      · exact Or.inl ((congrArg Prod.fst hw).trans hzroot)
      · rcases blowup_adj_skeleton G (matrix ω) hw with he | ha
        · exact Or.inl (he.symm.trans hzroot)
        · exact Or.inr ⟨w.1,hzroot ▸ ha,rfl⟩
    exact completed_candidate_simulation G pack enumeration A W T root (matrix ω) hu w hb
  · intro ω
    apply repaired_occupancy_measurable (H ω) (vertexClique root) (S ω)
    intro z
    by_cases hu : snapshotUnique pack T (fullEdgeSnapshot G (matrix ω) root) z.1
    · have h := hmeas (matrix ω) z
      simpa only [S,snapshotCandidates,Set.mem_setOf_eq,hu,true_and,
        fullSnapshotBlowup G (matrix ω) root,fullSnapshotIdentifiers G pack (matrix ω) root] using h
    · simp only [S,snapshotCandidates,Set.mem_setOf_eq,hu,false_and]
      exact MeasurableSet.empty
  · intro W
    exact concrete_fixed_table_occupancy G pack A W T hreg ht e hD hk hlower hupper

end TreeGeometry
end
end MISLocal
