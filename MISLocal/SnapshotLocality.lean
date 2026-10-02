import MISLocal.SnapshotAgreement

/-! A radius-(T+3) snapshot gives exactly the global candidate and repair
decisions at its root. This agreement is proved before invoking occupancy. -/

open scoped Classical
namespace MISLocal
noncomputable section

theorem repair_local_graph {X : Type*} (G H : SimpleGraph X) (S S' : Set X) (v : X)
    (hrow : ∀ w, G.Adj v w ↔ H.Adj v w) (hv : v ∈ S ↔ v ∈ S')
    (hn : ∀ w, G.Adj v w → (w ∈ S ↔ w ∈ S')) :
    v ∈ repair G S ↔ v ∈ repair H S' := by
  constructor
  · rintro ⟨hs,hns⟩
    refine ⟨hv.mp hs,fun w hw hsw => ?_⟩
    have hg := (hrow w).mpr hw
    exact hns w hg ((hn w hg).mpr hsw)
  · rintro ⟨hs,hns⟩
    exact ⟨hv.mpr hs,fun w hw hsw => hns w ((hrow w).mp hw) ((hn w hw).mp hsw)⟩

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m b : ℕ} (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    {Tape State : Type*} (A : UniformLocalProtocol (2^b) Tape State)
    (W : Fin (2^b) → Tape) (T : ℕ)

theorem snapshotUnique_agrees (M : G.edgeSet → EdgeMatrix (2*m)) (R c : ℕ) (root v : V)
    (hc : InBall G c root v) (hR : c+(T+1) ≤ R) :
    snapshotUnique pack T (edgeSnapshot G M (seen G (R+1) root) root) v ↔
      snapshotUnique pack T (fullEdgeSnapshot G M root) v := by
  let x := edgeSnapshot G M (seen G (R+1) root) root
  let y := fullEdgeSnapshot G M root
  have hb (z : V × Fin (2*m)) :
      InBall (snapshotSkeleton x) (T+1) v z.1 ↔ InBall (snapshotSkeleton y) (T+1) v z.1 := by
    dsimp [x,y]
    rw [fullSnapshotSkeleton G M root]
    exact snapshot_ball_agrees G M R c (T+1) root v z.1 hc hR
  have hi (z : V × Fin (2*m)) (hz : InBall (snapshotSkeleton y) (T+1) v z.1) :
      snapshotIdentifiers pack x z = snapshotIdentifiers pack y z := by
    rw [fullSnapshotSkeleton G M root] at hz
    exact snapshotIdentifiers_agrees G pack M _ root z (fun e he =>
      ball_incident_seen G (inBall_mono G hR (inBall_trans G hc hz)) e he)
  constructor
  · intro hu z hz w hw he
    apply hu ((hb z).mpr hz) ((hb w).mpr hw)
    rw [hi z hz,hi w hw]
    exact he
  · intro hu z hz w hw he
    apply hu ((hb z).mp hz) ((hb w).mp hw)
    rw [← hi z ((hb z).mp hz),← hi w ((hb w).mp hw)]
    exact he

theorem snapshotCandidates_agrees (M : G.edgeSet → EdgeMatrix (2*m)) (R c : ℕ)
    (root : V) (z : V × Fin (2*m)) (hc : InBall G c root z.1) (hR : c+(T+1) ≤ R) :
    z ∈ snapshotCandidates pack A W T (edgeSnapshot G M (seen G (R+1) root) root) ↔
      z ∈ snapshotCandidates pack A W T (fullEdgeSnapshot G M root) := by
  apply and_congr (snapshotUnique_agrees G pack T M R c root z.1 hc hR)
  let H := cliqueBlowup G M
  let x := edgeSnapshot G M (seen G (R+1) root) root
  let y := fullEdgeSnapshot G M root
  have hi (u : V × Fin (2*m)) (hu : InBall H (T+1) z u) :
      snapshotIdentifiers pack y u = snapshotIdentifiers pack x u := by
    exact (snapshotIdentifiers_agrees G pack M _ root u (fun e he =>
      ball_incident_seen G (inBall_mono G hR (inBall_trans G hc
        (blowup_ball_skeleton G M (T+1) z u hu))) e he)).symm
  have hr (u : V × Fin (2*m)) (hu : InBall H T z u) (w : V × Fin (2*m)) :
      H.Adj u w ↔ (snapshotBlowup x).Adj u w := by
    apply Iff.symm
    apply snapshotBlowup_row G M _ root u
    intro e he
    exact ball_incident_seen G (inBall_mono G (by omega) (inBall_trans G hc
      (blowup_ball_skeleton G M T z u hu))) e he
  have h := A.candidates_transport H (snapshotBlowup x) (Equiv.refl _)
    (snapshotIdentifiers pack y) (snapshotIdentifiers pack x) W T z hi hr
  dsimp only [H] at h
  rw [← fullSnapshotBlowup G M root] at h
  exact h.symm

theorem snapshotRepair_agrees (M : G.edgeSet → EdgeMatrix (2*m)) (root : V) (a : Fin (2*m)) :
    (root,a) ∈ repair (snapshotBlowup (edgeSnapshot G M (seen G (T+3) root) root))
      (snapshotCandidates pack A W T (edgeSnapshot G M (seen G (T+3) root) root)) ↔
    (root,a) ∈ repair (cliqueBlowup G M)
      (snapshotCandidates pack A W T (fullEdgeSnapshot G M root)) := by
  apply repair_local_graph
  · intro w
    exact snapshotBlowup_row G M _ root (root,a)
      (fun e he => ball_incident_seen G (inBall_self G (T+2) root) e he) w
  · exact snapshotCandidates_agrees G pack A W T M (T+2) 0 root (root,a) rfl (by omega)
  · intro w hw
    have ha : (cliqueBlowup G M).Adj (root,a) w :=
      (snapshotBlowup_row G M _ root (root,a)
        (fun e he => ball_incident_seen G (inBall_self G (T+2) root) e he) w).mp hw
    have hb : InBall G 1 root w.1 := by
      rcases blowup_adj_skeleton G M ha with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨w.1,h,rfl⟩
    exact snapshotCandidates_agrees G pack A W T M (T+2) 1 root w hb (by omega)

theorem snapshotCandidates_root_irrelevant (M : G.edgeSet → EdgeMatrix (2*m)) (v w : V) :
    snapshotCandidates pack A W T (fullEdgeSnapshot G M v) =
      snapshotCandidates pack A W T (fullEdgeSnapshot G M w) := rfl

theorem localAnonymousRule_representation
    (ω : ∀ i, matrixPrivateType G (2*m) (fun _ => Unit) i) (root : V) :
    runAnonymous G (localAnonymousRule pack A W T) (T+3) root ω =
      repairedLabel G (fun e => ω (Sum.inl e))
        (snapshotCandidates pack A W T (fullEdgeSnapshot G (fun e => ω (Sum.inl e)) root)) root := by
  change snapshotRepairedLabel pack A W T (namedLocalView G (T+3) root ω) = _
  have hv : namedLocalView G (T+3) root ω =
      edgeSnapshot G (fun e => ω (Sum.inl e)) (seen G (T+3) root) root := by
    have hc : ω (Sum.inr root) = () := @Subsingleton.elim Unit _ _ _
    simp only [namedLocalView,edgeSnapshot,hc]
  rw [hv]
  apply chooseLabel_congr
  exact snapshotRepair_agrees G pack A W T _ root

end TreeGeometry
end
end MISLocal
