import MISLocal.SnapshotLocality
import MISLocal.InfiniteTapes

/-! Legalize tentative IDs on the actual blow-up vertex set. The completion
is a genuine bijection and preserves the local IDs and ID-indexed tapes. -/

open scoped Classical
namespace MISLocal
noncomputable section

def completeVertexIDs {X : Type*} {n : ℕ} (enumeration : X ≃ Fin n)
    (U : Set X) (ids : X → Fin n) : X ≃ Fin n :=
  enumeration.trans (completeIDs {i | enumeration.symm i ∈ U}
    (fun i => ids (enumeration.symm i)))

theorem completeVertexIDs_agrees {X : Type*} {n : ℕ} (enumeration : X ≃ Fin n)
    (U : Set X) (ids : X → Fin n) (hinj : Set.InjOn ids U) (x : X) (hx : x ∈ U) :
    completeVertexIDs enumeration U ids x = ids x := by
  have hi : Set.InjOn (fun i => ids (enumeration.symm i)) {i | enumeration.symm i ∈ U} := by
    intro i hi j hj hij
    exact enumeration.symm.injective (hinj hi hj hij)
  change completeIDs _ _ (enumeration x) = _
  have ha := completeIDs_agrees {i | enumeration.symm i ∈ U}
    (fun i => ids (enumeration.symm i)) hi (enumeration x) (by simpa using hx)
  simpa only [enumeration.symm_apply_apply] using ha

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m b : ℕ} (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (enumeration : (V × Fin (2*m)) ≃ Fin (2^b))
    {Tape State : Type*} (A : UniformLocalProtocol (2^b) Tape State)
    (W : Fin (2^b) → Tape) (T : ℕ)

def locallyUniqueIDs (root : V) (M : G.edgeSet → EdgeMatrix (2*m)) : Prop :=
  Set.InjOn (extractedIdentifiers G pack M) {z | InBall G (T+2) root z.1}

def completedBlowupIDs (root : V) (M : G.edgeSet → EdgeMatrix (2*m)) :
    (V × Fin (2*m)) ≃ Fin (2^b) :=
  completeVertexIDs enumeration {z | InBall G (T+2) root z.1} (extractedIdentifiers G pack M)

omit [DecidableEq V] in
theorem completedBlowupIDs_agrees (root : V) (M : G.edgeSet → EdgeMatrix (2*m))
    (h : locallyUniqueIDs G pack T root M) (z : V × Fin (2*m))
    (hz : InBall G (T+2) root z.1) :
    completedBlowupIDs G pack enumeration T root M z = extractedIdentifiers G pack M z :=
  completeVertexIDs_agrees enumeration _ _ h z hz

/-- At the root and each adjacent clique, the collision-gated candidate
equals the actual execution on the legal completed ID assignment. -/
theorem completed_candidate_simulation (root : V) (M : G.edgeSet → EdgeMatrix (2*m))
    (h : locallyUniqueIDs G pack T root M) (z : V × Fin (2*m))
    (hz : InBall G 1 root z.1) :
    z ∈ snapshotCandidates pack A W T (fullEdgeSnapshot G M root) ↔
      z ∈ A.candidates (cliqueBlowup G M)
        (completedBlowupIDs G pack enumeration T root M) W T := by
  have hc (u : V × Fin (2*m)) (hu : InBall G (T+1) z.1 u.1) :
      InBall G (T+2) root u.1 := by
    simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using inBall_trans G hz hu
  have hu : snapshotUnique pack T (fullEdgeSnapshot G M root) z.1 := by
    unfold snapshotUnique
    rw [fullSnapshotIdentifiers G pack M root,fullSnapshotSkeleton G M root]
    exact fun u huu v hvv huv => h (hc u huu) (hc v hvv) huv
  change (_ ∧ _) ↔ _
  simp only [hu,true_and]
  rw [fullSnapshotIdentifiers G pack M root,fullSnapshotBlowup G M root]
  apply A.candidates_local
  intro u huu
  exact (completedBlowupIDs_agrees G pack enumeration T root M h u
    (hc u (blowup_ball_skeleton G M (T+1) z u huu))).symm

end TreeGeometry
end
end MISLocal
