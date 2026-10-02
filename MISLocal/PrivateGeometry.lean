import MISLocal.InputGeometry
import MISLocal.PrivateSources

/-! An independent final random draw at each vertex requires no extra
round. Its coordinate is included among that vertex's readers, but never
among the conditioned edge-input views. -/

open scoped Classical

namespace MISLocal
noncomputable section

def ProductInputGeometry.withPrivate {I V E : Type*}
    [DecidableEq I] [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {d r : ℕ} (g : ProductInputGeometry I V E d r) :
    ProductInputGeometry (I ⊕ V) V E d r where
  left := g.left
  right := g.right
  noLoop := g.noLoop
  degree := g.degree
  edgeCount := g.edgeCount
  readers := privateReads g.readers
  vertex := fun j v => rawView (g.vertex j v)
  shared := fun j e => rawView (g.shared j e)
  vertex_readers := by
    intro j v hj
    exact (Finset.map_subset_map.mpr (g.vertex_readers j v hj)).trans Finset.subset_union_left
  nested := fun j v hj => Finset.map_subset_map.mpr (g.nested j v hj)
  empty_last := fun v => by simp [g.empty_last, rawView]
  contains := fun j v e hj hv => Finset.map_subset_map.mpr (g.contains j v e hj hv)
  shared_inside := fun j v e hj hv => Finset.map_subset_map.mpr (g.shared_inside j v e hj hv)
  endpoint_overlap := by
    intro j e hj i hi
    cases i with
    | inl i =>
      have h : i ∈ g.vertex j (g.left e) ∩ g.vertex j (g.right e) := by simpa [rawView] using hi
      simpa [rawView] using g.endpoint_overlap j e hj h
    | inr v => simp [rawView] at hi
  branch_overlap := by
    intro j v e f hj hef hve hvf i hi
    cases i with
    | inl i =>
      have h : i ∈ g.shared j e ∩ g.shared j f := by simpa [rawView] using hi
      simpa [rawView] using g.branch_overlap j v e f hj hef hve hvf h
    | inr v => simp [rawView] at hi
  initial_reader_overlap := by
    intro e i hi
    cases i with
    | inl i =>
      have h : i ∈ g.readers (g.left e) ∩ g.readers (g.right e) := by
        simpa [privateReads, rawView] using hi
      simpa [rawView] using g.initial_reader_overlap e h
    | inr v =>
      have h : v = g.left e ∧ v = g.right e := by simpa [privateReads, rawView] using hi
      exact False.elim (g.noLoop e (h.2.symm.trans h.1))
  initial_shared_overlap := by
    intro v e hv i hi
    cases i with
    | inl i =>
      have h : i ∈ g.readers v ∩ g.shared 0 e := by simpa [privateReads, rawView] using hi
      simpa [rawView] using g.initial_shared_overlap v e hv h
    | inr v => simp [privateReads, rawView] at hi
  charge := fun j hj => (g.charge j hj).withPrivate g.degree (g.contains j · · hj)

end
end MISLocal
