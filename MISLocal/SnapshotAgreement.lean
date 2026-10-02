import MISLocal.AnonymousLocalReduction

/-! A snapshot contains every row and extracted ID whose incident skeleton
edges are visible. This is the concrete link from a quotient rule to the
single global repaired candidate set. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

theorem inBall_trans {V : Type*} (G : SimpleGraph V) {s t : ℕ} {v w u : V}
    (hvw : InBall G s v w) (hwu : InBall G t w u) : InBall G (s+t) v u := by
  induction t generalizing s w with
  | zero => simpa using hwu ▸ hvw
  | succ t ih =>
    rcases hwu with hwu | ⟨z,hwz,hzu⟩
    · subst u; exact inBall_mono G (by omega) hvw
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (inBall_append G s hvw hwz) hzu

theorem inBall_map_le {V : Type*} {G H : SimpleGraph V} (h : G ≤ H)
    (t : ℕ) (v u : V) (hb : InBall G t v u) : InBall H t v u := by
  induction t generalizing v u with
  | zero => exact hb
  | succ t ih =>
    rcases hb with he | ⟨w,hvw,hwu⟩
    · exact Or.inl he
    · exact Or.inr ⟨w,h hvw,ih w u hwu⟩

theorem inBall_local_rows {V : Type*} (G H : SimpleGraph V) (t : ℕ) (v u : V)
    (hrows : ∀ w, InBall G t v w → ∀ z, G.Adj w z ↔ H.Adj w z)
    (hb : InBall G t v u) : InBall H t v u := by
  induction t generalizing v u with
  | zero => exact hb
  | succ t ih =>
    rcases hb with he | ⟨w,hvw,hwu⟩
    · exact Or.inl he
    · exact Or.inr ⟨w,(hrows v (inBall_self G (t+1) v) w).mp hvw,
        ih w u (fun z hz => hrows z (Or.inr ⟨w,hvw,hz⟩)) hwu⟩

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}

def edgeSnapshot (M : G.edgeSet → EdgeMatrix k) (S : Finset G.edgeSet) (v : V) :
    NamedLocalView V G.edgeSet k Unit where
  root := v
  coin := ()
  edges e := if e ∈ S then some (edgeLeft G e,edgeRight G e,M e) else none

def fullEdgeSnapshot (M : G.edgeSet → EdgeMatrix k) (v : V) :
    NamedLocalView V G.edgeSet k Unit := edgeSnapshot G M Finset.univ v

omit [Fintype V] [DecidableRel G.Adj] in
theorem snapshotSkeleton_le (M : G.edgeSet → EdgeMatrix k) (S : Finset G.edgeSet) (v : V) :
    snapshotSkeleton (edgeSnapshot G M S v) ≤ G := by
  rintro a b ⟨_,e,z,he,hz⟩
  have hes : e ∈ S := by
    by_contra hn
    simp [edgeSnapshot,hn] at he
  have hez : (edgeLeft G e,edgeRight G e,M e) = z := by
    simpa [edgeSnapshot,hes] using he
  subst z
  rcases hz with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [← ha,← hb]; exact endpoint_adj G e
  · rw [← ha,← hb]; exact (endpoint_adj G e).symm

theorem fullSnapshotSkeleton (M : G.edgeSet → EdgeMatrix k) (v : V) :
    snapshotSkeleton (fullEdgeSnapshot G M v) = G := by
  apply le_antisymm (snapshotSkeleton_le G M Finset.univ v)
  intro a b hab
  let e : G.edgeSet := ⟨s(a,b),hab⟩
  have hp : s(edgeLeft G e,edgeRight G e) = s(a,b) := edge_endpoints G e
  refine ⟨hab.ne,e,(edgeLeft G e,edgeRight G e,M e),?_,?_⟩
  · simp [fullEdgeSnapshot,edgeSnapshot]
  · rcases Sym2.eq_iff.mp hp with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2,h.1⟩

theorem fullSnapshotBlowup (M : G.edgeSet → EdgeMatrix k) (v : V) :
    snapshotBlowup (fullEdgeSnapshot G M v) = cliqueBlowup G M := by
  ext x y
  constructor
  · rintro (h | ⟨_,e,z,he,hz⟩)
    · exact Or.inl h
    · have hez : (edgeLeft G e,edgeRight G e,M e) = z := by
        simpa [fullEdgeSnapshot,edgeSnapshot] using he
      subst z
      exact Or.inr ⟨e,hz⟩
  · rintro (h | ⟨e,hz⟩)
    · exact Or.inl h
    · have ha := crossCliqueAdj_skeleton G M (show crossCliqueAdj G M x y from ⟨e,hz⟩)
      exact Or.inr ⟨ha.ne,e,(edgeLeft G e,edgeRight G e,M e),
        by simp [fullEdgeSnapshot,edgeSnapshot],hz⟩

theorem snapshotSkeleton_row (M : G.edgeSet → EdgeMatrix k) (S : Finset G.edgeSet)
    (root v : V) (hsee : ∀ e, edgeIncident (edgeLeft G) (edgeRight G) v e → e ∈ S) (w : V) :
    (snapshotSkeleton (edgeSnapshot G M S root)).Adj v w ↔ G.Adj v w := by
  constructor
  · exact fun h => snapshotSkeleton_le G M S root h
  · intro hvw
    have ha : (snapshotSkeleton (fullEdgeSnapshot G M root)).Adj v w := by
      rw [fullSnapshotSkeleton G M root]; exact hvw
    obtain ⟨hne,e,z,he,hz⟩ := ha
    have hez : (edgeLeft G e,edgeRight G e,M e) = z := by
      simpa [fullEdgeSnapshot,edgeSnapshot] using he
    subst z
    have hi : edgeIncident (edgeLeft G) (edgeRight G) v e :=
      hz.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    exact ⟨hne,e,(edgeLeft G e,edgeRight G e,M e),by simp [edgeSnapshot,hsee e hi],hz⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem snapshotBlowup_row (M : G.edgeSet → EdgeMatrix k) (S : Finset G.edgeSet)
    (root : V) (v : V × Fin k)
    (hsee : ∀ e, edgeIncident (edgeLeft G) (edgeRight G) v.1 e → e ∈ S)
    (w : V × Fin k) :
    (snapshotBlowup (edgeSnapshot G M S root)).Adj v w ↔ (cliqueBlowup G M).Adj v w := by
  constructor
  · rintro (h | ⟨_,e,z,he,hz⟩)
    · exact Or.inl h
    · have hes : e ∈ S := by by_contra hn; simp [edgeSnapshot,hn] at he
      have hez : (edgeLeft G e,edgeRight G e,M e) = z := by simpa [edgeSnapshot,hes] using he
      subst z
      exact Or.inr ⟨e,hz⟩
  · rintro (h | ⟨e,hz⟩)
    · exact Or.inl h
    · have hi : edgeIncident (edgeLeft G) (edgeRight G) v.1 e :=
        hz.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      have ha := crossCliqueAdj_skeleton G M (show crossCliqueAdj G M v w from ⟨e,hz⟩)
      exact Or.inr ⟨ha.ne,e,(edgeLeft G e,edgeRight G e,M e),
        by simp [edgeSnapshot,hsee e hi],hz⟩

omit [DecidableEq V] in
theorem ball_incident_seen {r : ℕ} {root v : V} (hb : InBall G r root v)
    (e : G.edgeSet) (hi : edgeIncident (edgeLeft G) (edgeRight G) v e) :
    e ∈ seen G (r+1) root :=
  (seen_ball G r root e).mpr ⟨v,(incident_iff_mem G v e).mp hi,hb⟩

theorem snapshotBlockStrings_agrees {m : ℕ} (M : G.edgeSet → EdgeMatrix (2*m))
    (S : Finset G.edgeSet) (root v : V)
    (hsee : ∀ e, edgeIncident (edgeLeft G) (edgeRight G) v e → e ∈ S) :
    snapshotBlockStrings m (edgeSnapshot G M S root) v =
      snapshotBlockStrings m (fullEdgeSnapshot G M root) v := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ S
  · simp [edgeSnapshot,fullEdgeSnapshot,he]
  · have hl : edgeLeft G e ≠ v := fun h => he (hsee e (Or.inl h))
    have hr : edgeRight G e ≠ v := fun h => he (hsee e (Or.inr h))
    funext p
    simp [edgeSnapshot,fullEdgeSnapshot,he,datumBlockString,hl,hr]

theorem fullSnapshotBlockStrings {m : ℕ} (M : G.edgeSet → EdgeMatrix (2*m)) (root v : V) :
    snapshotBlockStrings m (fullEdgeSnapshot G M root) v = extractedBlockStrings G m M v := by
  funext p
  simp only [snapshotBlockStrings,fullEdgeSnapshot,edgeSnapshot,Finset.mem_univ,if_true,
    Option.elim_some,Finset.sum_apply,extractedBlockStrings,vertexBlockSum,AddMonoidHom.comp_apply,
    endpointSum,blockRestriction,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Fintype.sum_prod_type,
    Fintype.sum_bool,outgoingEndpoint,if_true,Bool.false_eq_true,if_false,matrixBitGroupEquiv,
    datumBlockString,Pi.zero_apply]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.sum_apply,Pi.zero_apply,Pi.add_apply]
  by_cases hl : edgeLeft G e = v <;> by_cases hr : edgeRight G e = v <;>
    simp [hl,hr,matrixBitGroupEquiv,add_comm]

theorem fullSnapshotIdentifiers {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (M : G.edgeSet → EdgeMatrix (2*m)) (root : V) :
    snapshotIdentifiers pack (fullEdgeSnapshot G M root) = extractedIdentifiers G pack M := by
  funext va
  unfold snapshotIdentifiers
  rw [fullSnapshotBlockStrings G M root va.1]
  rfl

theorem snapshotIdentifiers_agrees {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (M : G.edgeSet → EdgeMatrix (2*m)) (S : Finset G.edgeSet) (root : V)
    (va : V × Fin (2*m))
    (hsee : ∀ e, edgeIncident (edgeLeft G) (edgeRight G) va.1 e → e ∈ S) :
    snapshotIdentifiers pack (edgeSnapshot G M S root) va =
      snapshotIdentifiers pack (fullEdgeSnapshot G M root) va := by
  unfold snapshotIdentifiers
  rw [snapshotBlockStrings_agrees G M S root va.1 hsee]

theorem snapshot_ball_agrees (M : G.edgeSet → EdgeMatrix k) (R c s : ℕ) (root v u : V)
    (hc : InBall G c root v) (hcs : c+s ≤ R) :
    InBall (snapshotSkeleton (edgeSnapshot G M (seen G (R+1) root) root)) s v u ↔
      InBall G s v u := by
  constructor
  · exact inBall_map_le (snapshotSkeleton_le G M (seen G (R+1) root) root) s v u
  · apply inBall_local_rows G _ s v u
    intro w hw z
    exact (snapshotSkeleton_row G M (seen G (R+1) root) root w
      (fun e he => ball_incident_seen G (inBall_mono G hcs (inBall_trans G hc hw)) e he) z).symm

end TreeGeometry
end
end MISLocal
