import MISLocal.EntropyCharging
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Parent edges in an actual simple tree. No entropy assumptions occur here. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

namespace TreeGeometry

variable {V : Type*} {G : SimpleGraph V}

def rootPath (hG : G.IsTree) (root v : V) : G.Walk v root :=
  (hG.existsUnique_path v root).choose

theorem rootPath_isPath (hG : G.IsTree) (root v : V) : (rootPath hG root v).IsPath :=
  (hG.existsUnique_path v root).choose_spec.1

theorem rootPath_unique (hG : G.IsTree) (root v : V) (p : G.Walk v root) (hp : p.IsPath) :
    p = rootPath hG root v := (hG.existsUnique_path v root).choose_spec.2 p hp

def parentDart (hG : G.IsTree) (root : V) (v : {v // v ≠ root}) : G.Dart :=
  (rootPath hG root v.val).firstDart (SimpleGraph.Walk.not_nil_of_ne v.property)

@[simp] theorem parentDart_fst (hG : G.IsTree) (root : V) (v : {v // v ≠ root}) :
    (parentDart hG root v).fst = v.val := rfl

theorem parent_length (hG : G.IsTree) (root : V) (v : {v // v ≠ root}) :
    (rootPath hG root v.val).length =
      (rootPath hG root (parentDart hG root v).snd).length+1 := by
  have ht := rootPath_unique hG root (rootPath hG root v.val).snd
    (rootPath hG root v.val).tail (rootPath_isPath hG root v.val).tail
  have hl := SimpleGraph.Walk.length_tail_add_one
    (SimpleGraph.Walk.not_nil_of_ne v.property : ¬ (rootPath hG root v.val).Nil)
  rw [ht] at hl
  exact hl.symm

def parentEdge (hG : G.IsTree) (root : V) (v : {v // v ≠ root}) : G.edgeSet :=
  ⟨(parentDart hG root v).edge, (parentDart hG root v).edge_mem⟩

theorem parentEdge_injective (hG : G.IsTree) (root : V) :
    Function.Injective (parentEdge hG root) := by
  intro v w h
  have he := congrArg Subtype.val h
  change (parentDart hG root v).edge = (parentDart hG root w).edge at he
  rcases (SimpleGraph.dart_edge_eq_iff _ _).mp he with hd | hd
  · apply Subtype.ext
    exact congrArg (fun d : G.Dart => d.fst) hd
  · have hv : (parentDart hG root v).snd = w.val := congrArg (fun d : G.Dart => d.snd) hd
    have hw : (parentDart hG root w).snd = v.val := (congrArg (fun d : G.Dart => d.fst) hd).symm
    have hlv := parent_length hG root v
    have hlw := parent_length hG root w
    rw [hv] at hlv
    rw [hw] at hlw
    omega

/-- Every edge of a finite tree is the parent edge of exactly one nonroot
vertex. The cardinality cancellation is justified with a nonempty vertex
type, so no truncated subtraction can silently discard a case. -/
theorem parentEdge_bijective [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsTree) (root : V) :
    Function.Bijective (parentEdge hG root) := by
  classical
  letI : Nonempty V := ⟨root⟩
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨parentEdge_injective hG root, ?_⟩
  have hc := hG.card_edgeFinset
  rw [G.edgeFinset_card] at hc
  have hsingle : Fintype.card {v : V // v = root} = 1 := by
    letI : Unique {v : V // v = root} := ⟨⟨⟨root,rfl⟩⟩, fun v => Subtype.ext v.property⟩
    exact Fintype.card_unique
  have hsub := Fintype.card_subtype_compl (fun v : V => v = root)
  rw [hsingle] at hsub
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  calc
    _ = Fintype.card V - 1 := hsub
    _ = _ := by omega

/-- If an edge joins two vertices, one of those vertices has that edge as
its parent. This is the exclusion needed for injective outward charging. -/
theorem edge_has_parent_endpoint [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsTree) (root : V)
    (v w : V) (hvw : G.Adj v w) :
    (∃ hv : v ≠ root, (parentEdge hG root ⟨v,hv⟩).val = s(v,w)) ∨
      (∃ hw : w ≠ root, (parentEdge hG root ⟨w,hw⟩).val = s(v,w)) := by
  obtain ⟨u, hu⟩ := (parentEdge_bijective hG root).2 ⟨s(v,w),hvw⟩
  have he : (parentDart hG root u).edge = s(v,w) := congrArg Subtype.val hu
  have hmem : u.val ∈ s(v,w) := by
    rw [← he]
    exact Sym2.mem_mk_left _ _
  rcases Sym2.mem_iff.mp hmem with huv | huw
  · left
    subst v
    exact ⟨u.property, he⟩
  · right
    subst w
    exact ⟨u.property, he⟩

/-- In a tree, the path to the root stays in every connected induced vertex
set containing both endpoints. This is the geometric reason that an edge
entering an already-observed inner neighborhood must be the parent edge. -/
theorem rootPath_support_subset (hG : G.IsTree) (root : V) (K : Set V)
    (hK : (G.induce K).Connected) (hroot : root ∈ K) {v : V} (hv : v ∈ K) :
    ∀ w ∈ (rootPath hG root v).support, w ∈ K := by
  obtain ⟨p,hp⟩ := hK.exists_isPath ⟨v,hv⟩ ⟨root,hroot⟩
  let emb : G.induce K ↪g G := SimpleGraph.Embedding.induce K
  have hpath := SimpleGraph.Walk.map_isPath_of_injective (f := emb.toHom) emb.injective hp
  have heq := rootPath_unique hG root v (p.map emb.toHom) hpath
  intro w hw
  rw [← heq, SimpleGraph.Walk.support_map] at hw
  obtain ⟨x,_,hx⟩ := List.mem_map.mp hw
  rw [← hx]
  exact x.property

theorem parent_stays_in_connected_set (hG : G.IsTree) (root : V) (K : Set V)
    (hK : (G.induce K).Connected) (hroot : root ∈ K)
    (v : {v // v ≠ root}) (hv : v.val ∈ K) : (parentDart hG root v).snd ∈ K := by
  exact rootPath_support_subset hG root K hK hroot hv _
    ((rootPath hG root v.val).getVert_mem_support 1)

theorem parent_of_edge_into_connected_set [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsTree) (root : V) (K : Set V) (hK : (G.induce K).Connected)
    (hroot : root ∈ K) {v w : V} (hv : v ∉ K) (hw : w ∈ K) (hvw : G.Adj v w) :
    ∃ hvr : v ≠ root, (parentEdge hG root ⟨v,hvr⟩).val = s(v,w) := by
  rcases edge_has_parent_endpoint hG root v w hvw with hp | ⟨hwr, hp⟩
  · exact hp
  · have hnext := parent_stays_in_connected_set hG root K hK hroot ⟨w,hwr⟩ hw
    have hmem : v ∈ (parentDart hG root ⟨w,hwr⟩).edge := by
      change v ∈ (parentEdge hG root ⟨w,hwr⟩).val
      rw [hp]
      exact Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hmem with h | h
    · exact False.elim (hv (h ▸ hw))
    · exact False.elim (hv (h ▸ hnext))

end TreeGeometry
end
end MISLocal
