import MISLocal.TreeParent
import MISLocal.ParentCharging

/-! Source routing on a finite regular graph whose individual reader regions
are induced trees. The ambient graph is NOT assumed to be a finite regular
tree (which would make the hypotheses impossible at degree at least two). -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

def edgeLeft (e : G.edgeSet) : V := e.val.out.1
def edgeRight (e : G.edgeSet) : V := e.val.out.2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edge_endpoints (e : G.edgeSet) : s(edgeLeft G e,edgeRight G e) = e.val :=
  Quot.out_eq e.val

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem incident_iff_mem (v : V) (e : G.edgeSet) :
    edgeIncident (edgeLeft G) (edgeRight G) v e ↔ v ∈ e.val := by
  rw [← edge_endpoints G e, Sym2.mem_iff]
  simp only [edgeIncident, eq_comm]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edge_eq_of_incident {v w : V} (hvw : v ≠ w) (e : G.edgeSet)
    (hv : edgeIncident (edgeLeft G) (edgeRight G) v e)
    (hw : edgeIncident (edgeLeft G) (edgeRight G) w e) : e.val = s(v,w) := by
  exact (Sym2.mem_and_mem_iff hvw).mp
    ⟨(incident_iff_mem G v e).mp hv,(incident_iff_mem G w e).mp hw⟩

def regionParent (W : Set V) (ht : (G.induce W).IsTree) (root : W)
    (anchor : G.edgeSet) (v : W) : G.edgeSet :=
  if hv : v = root then anchor else
    (SimpleGraph.Embedding.induce W).toHom.mapEdgeSet (parentEdge ht root ⟨v,hv⟩)

omit [Fintype V] [DecidableRel G.Adj] in
theorem regionParent_incident (W : Set V) (ht : (G.induce W).IsTree) (root : W)
    (anchor : G.edgeSet) (ha : root.val ∈ anchor.val) (v : W) :
    v.val ∈ (regionParent G W ht root anchor v).val := by
  unfold regionParent
  split_ifs with hv
  · simpa [hv] using ha
  · change v.val ∈ s(v.val,(parentDart ht root ⟨v,hv⟩).snd.val)
    exact Sym2.mem_mk_left _ _

omit [Fintype V] [DecidableRel G.Adj] in
theorem regionParent_of_tree_parent (W : Set V) (ht : (G.induce W).IsTree)
    (root : W) (anchor : G.edgeSet) (v w : W) (hv : v ≠ root)
    (hp : (parentEdge ht root ⟨v,hv⟩).val = s(v,w)) :
    (regionParent G W ht root anchor v).val = s(v.val,w.val) := by
  simp only [regionParent, dif_neg hv]
  change Sym2.map Subtype.val (parentEdge ht root ⟨v,hv⟩).val = _
  rw [hp]
  rfl

theorem regionParent_cover (W : Set V) (ht : (G.induce W).IsTree)
    (root : W) (anchor : G.edgeSet) (v w : W) (hvw : G.Adj v.val w.val) :
    (regionParent G W ht root anchor v).val = s(v.val,w.val) ∨
      (regionParent G W ht root anchor w).val = s(v.val,w.val) := by
  rcases edge_has_parent_endpoint ht root v w hvw with ⟨hv,hp⟩ | ⟨hw,hp⟩
  · exact Or.inl (regionParent_of_tree_parent G W ht root anchor v w hv hp)
  · exact Or.inr (by
      rw [Sym2.eq_swap] at hp
      simpa only [Sym2.eq_swap] using
        regionParent_of_tree_parent G W ht root anchor w v hw hp)

theorem regionParent_anchor (W : Set V) (ht : (G.induce W).IsTree)
    (root : W) (anchor : G.edgeSet) (ha : root.val ∈ anchor.val) (v : W)
    (hv : v.val ∈ anchor.val) : regionParent G W ht root anchor v = anchor := by
  by_cases he : v = root
  · simp [regionParent, he]
  · have hne : v.val ≠ root.val := fun h => he (Subtype.ext h)
    have hae : anchor.val = s(v.val,root.val) := (Sym2.mem_and_mem_iff hne).mp ⟨hv,ha⟩
    have hadj : (G.induce W).Adj v root := by
      have h := anchor.property
      rw [hae] at h
      exact h
    rcases edge_has_parent_endpoint ht root v root hadj with ⟨hv',hp⟩ | ⟨hr,_⟩
    · apply Subtype.ext
      rw [regionParent_of_tree_parent G W ht root anchor v root hv' hp, hae]
    · exact False.elim (hr rfl)

/-- Reader regions and their already-observed inner regions are genuine
induced trees/connected sets. These purely geometric assumptions suffice to
CONSTRUCT the source-charge certificate, rather than postulate its routes. -/
def sourceChargeOfReaderTrees {I : Type*} [DecidableEq I]
    (reads vertexView : V → Finset I) (edgeView : G.edgeSet → Finset I) (d : ℕ)
    (root : ∀ i, {v // i ∈ reads v}) (anchor : I → G.edgeSet)
    (ht : ∀ i, (G.induce {v | i ∈ reads v}).IsTree)
    (ha : ∀ i, (root i).val ∈ (anchor i).val)
    (hdegree : ∀ v, (Finset.univ.filter
      (edgeIncident (edgeLeft G) (edgeRight G) v)).card = d+1)
    (hknown : ∀ v, vertexView v ⊆ reads v)
    (hinner : ∀ i v, i ∈ vertexView v →
      i ∈ vertexView (root i).val ∧
        ((G.induce {v | i ∈ reads v}).induce
          {w | i ∈ vertexView w.val}).Connected)
    (hedge : ∀ i e, i ∈ edgeView e →
      i ∈ vertexView (edgeLeft G e) ∨ i ∈ vertexView (edgeRight G e) ∨ e = anchor i)
    (hcontains : ∀ v e, edgeIncident (edgeLeft G) (edgeRight G) v e →
      vertexView v ⊆ edgeView e) :
    SourceCharge (edgeLeft G) (edgeRight G) reads vertexView edgeView d := by
  let parent := fun i (v : {v // i ∈ reads v ∧ i ∉ vertexView v}) =>
    regionParent G {v | i ∈ reads v} (ht i) (root i) (anchor i) ⟨v.val,v.property.1⟩
  apply sourceChargeOfParents (edgeLeft G) (edgeRight G) reads vertexView edgeView d parent hdegree
  · intro i v
    exact (incident_iff_mem G _ _).mpr
      (regionParent_incident G _ (ht i) (root i) (anchor i) (ha i) _)
  · intro i v w hne e hv hw
    have he := edge_eq_of_incident G hne e hv hw
    have hadj : G.Adj v.val w.val := by simpa only [he] using e.property
    rcases regionParent_cover G _ (ht i) (root i) (anchor i)
      ⟨v.val,v.property.1⟩ ⟨w.val,w.property.1⟩ hadj with hp | hp
    · exact Or.inl (Subtype.ext (he.trans hp.symm))
    · exact Or.inr (Subtype.ext (he.trans hp.symm))
  · intro i v e hv hi
    have henter (w : V) (hw : i ∈ vertexView w)
        (hwe : edgeIncident (edgeLeft G) (edgeRight G) w e) : e = parent i v := by
      have hvw : v.val ≠ w := fun h => v.property.2 (h ▸ hw)
      have he := edge_eq_of_incident G hvw e hv hwe
      have hadj : G.Adj v.val w := by simpa only [he] using e.property
      obtain ⟨hroot,hconn⟩ := hinner i w hw
      obtain ⟨hvr,hp⟩ := parent_of_edge_into_connected_set (ht i) (root i)
        {w | i ∈ vertexView w.val} hconn hroot
        (v := ⟨v.val,v.property.1⟩) (w := ⟨w,hknown w hw⟩) v.property.2 hw hadj
      apply Subtype.ext
      exact he.trans (regionParent_of_tree_parent G _ (ht i) (root i) (anchor i)
        ⟨v.val,v.property.1⟩ ⟨w,hknown w hw⟩ hvr hp).symm
    rcases hedge i e hi with hl | hr | he
    · exact henter _ hl (Or.inl rfl)
    · exact henter _ hr (Or.inr rfl)
    · subst e
      exact (regionParent_anchor G _ (ht i) (root i) (anchor i) (ha i)
        ⟨v.val,v.property.1⟩ ((incident_iff_mem G _ _).mp hv)).symm
  · exact hcontains

end TreeGeometry
end
end MISLocal
