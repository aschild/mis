import MISLocal.GeometricCharging
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Actual edge-centered neighborhoods. Connectivity, nesting, and the
separation of successive layers are proved here, not taken as probabilistic
model assumptions. -/

open scoped Classical

namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type*} (G : SimpleGraph V)

def expand (K : Set V) : Set V := {v | v ∈ K ∨ ∃ w ∈ K, G.Adj v w}

theorem subset_expand (K : Set V) : K ⊆ expand G K := fun _ hv => Or.inl hv

theorem expand_mono {K L : Set V} (h : K ⊆ L) : expand G K ⊆ expand G L := by
  rintro v (hv | ⟨w,hw,hvw⟩)
  · exact Or.inl (h hv)
  · exact Or.inr ⟨w,h hw,hvw⟩

def edgeRegion (e : G.edgeSet) : ℕ → Set V
  | 0 => {v | v ∈ e.val}
  | t+1 => expand G (edgeRegion e t)

theorem edgeRegion_step (e : G.edgeSet) (t : ℕ) :
    edgeRegion G e t ⊆ edgeRegion G e (t+1) := subset_expand G _

theorem edgeRegion_mono (e : G.edgeSet) {s t : ℕ} (h : s ≤ t) :
    edgeRegion G e s ⊆ edgeRegion G e t := by
  induction h with
  | refl => exact Set.Subset.refl _
  | @step t h ih => exact ih.trans (edgeRegion_step G e t)

theorem endpoint_mem_region (e : G.edgeSet) (t : ℕ) {v : V} (hv : v ∈ e.val) :
    v ∈ edgeRegion G e t := edgeRegion_mono G e (Nat.zero_le t) hv

theorem expand_connected (K : Set V) (hK : (G.induce K).Connected) :
    (G.induce (expand G K)).Connected := by
  obtain ⟨root⟩ := hK.nonempty
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨root.val,Or.inl root.property⟩,?_⟩
  rintro ⟨v,hv⟩
  let f := (G.induceHomOfLE (subset_expand G K)).toHom
  rcases hv with hv | ⟨w,hw,hvw⟩
  · exact (hK root ⟨v,hv⟩).map f
  · exact ((hK root ⟨w,hw⟩).map f).trans
      (SimpleGraph.Adj.reachable (G := G.induce (expand G K))
        (u := ⟨w,Or.inl hw⟩) (v := ⟨v,Or.inr ⟨w,hw,hvw⟩⟩) hvw.symm)

theorem edgeRegion_connected (e : G.edgeSet) (t : ℕ) :
    (G.induce (edgeRegion G e t)).Connected := by
  induction t with
  | zero =>
    have he : edgeRegion G e 0 = {edgeLeft G e,edgeRight G e} := by
      ext v
      simp only [edgeRegion, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [← edge_endpoints G e, Sym2.mem_iff]
    rw [he]
    apply SimpleGraph.induce_pair_connected_of_adj
    have hp := e.property
    rw [← edge_endpoints G e] at hp
    exact hp
  | succ t ih => exact expand_connected G _ ih

theorem acyclic_of_embedding {W : Type*} {H : SimpleGraph W}
    (f : H ↪g G) (hG : G.IsAcyclic) : H.IsAcyclic := by
  intro v p hp
  exact hG (p.map f.toHom) (hp.map f.injective)

theorem induced_region_tree (e : G.edgeSet) {s t : ℕ} (hst : s ≤ t)
    (ht : (G.induce (edgeRegion G e t)).IsTree) :
    (G.induce (edgeRegion G e s)).IsTree :=
  ⟨edgeRegion_connected G e s,
    acyclic_of_embedding _ (G.induceHomOfLE (edgeRegion_mono G e hst)) ht.IsAcyclic⟩

/-- Re-inducing a connected subset inside a larger induced graph preserves
connectivity. The explicit embedding prevents subtype coercions from hiding
an extra geometric hypothesis. -/
theorem connected_inside {K W : Set V} (hKW : K ⊆ W)
    (hK : (G.induce K).Connected) :
    ((G.induce W).induce {v | v.val ∈ K}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨root⟩ := hK.nonempty
  let f : G.induce K →g (G.induce W).induce {v | v.val ∈ K} :=
    ⟨fun v => ⟨⟨v.val,hKW v.property⟩,v.property⟩,fun h => h⟩
  refine ⟨f root,?_⟩
  intro v
  exact (hK root ⟨v.val.val,v.property⟩).map f

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In a tree, the new outer layer of the expansion of a connected set is
independent. A hypothetical edge would have two distinct inward parents. -/
theorem outer_layer_independent (ht : G.IsTree) (K : Set V)
    (hK : (G.induce K).Connected) {v w : V}
    (hv : v ∈ expand G K) (hw : w ∈ expand G K)
    (hvn : v ∉ K) (hwn : w ∉ K) : ¬ G.Adj v w := by
  obtain ⟨root⟩ := hK.nonempty
  obtain ⟨a,ha,hva⟩ := hv.resolve_left hvn
  obtain ⟨b,hb,hwb⟩ := hw.resolve_left hwn
  obtain ⟨hvr,hvp⟩ := parent_of_edge_into_connected_set ht root.val K hK root.property hvn ha hva
  obtain ⟨hwr,hwp⟩ := parent_of_edge_into_connected_set ht root.val K hK root.property hwn hb hwb
  intro hvw
  rcases edge_has_parent_endpoint ht root.val v w hvw with ⟨_,hp⟩ | ⟨_,hp⟩
  · have he : s(v,a) = s(v,w) := hvp.symm.trans hp
    have ham : a ∈ s(v,w) := he ▸ Sym2.mem_mk_right v a
    rcases Sym2.mem_iff.mp ham with heq | heq
    · exact hvn (heq ▸ ha)
    · exact hwn (heq ▸ ha)
  · have he : s(w,b) = s(v,w) := hwp.symm.trans hp
    have hbm : b ∈ s(v,w) := he ▸ Sym2.mem_mk_right w b
    rcases Sym2.mem_iff.mp hbm with heq | heq
    · exact hvn (heq ▸ hb)
    · exact hwn (heq ▸ hb)

theorem unique_neighbor_into_connected_set (ht : G.IsTree) (K : Set V)
    (hK : (G.induce K).Connected) {v w z : V}
    (hv : v ∉ K) (hw : w ∈ K) (hz : z ∈ K)
    (hvw : G.Adj v w) (hvz : G.Adj v z) : w = z := by
  obtain ⟨root⟩ := hK.nonempty
  obtain ⟨_,hp⟩ := parent_of_edge_into_connected_set ht root.val K hK root.property hv hw hvw
  obtain ⟨_,hq⟩ := parent_of_edge_into_connected_set ht root.val K hK root.property hv hz hvz
  have he : s(v,w) = s(v,z) := hp.symm.trans hq
  have hm : w ∈ s(v,z) := he ▸ Sym2.mem_mk_right v w
  rcases Sym2.mem_iff.mp hm with h | h
  · exact False.elim (hv (h ▸ hw))
  · exact h

theorem adjacent_region_step (e : G.edgeSet) (t : ℕ)
    (ht : (G.induce (edgeRegion G e (t+1))).IsTree) {v w : V}
    (hv : v ∈ edgeRegion G e (t+1)) (hw : w ∈ edgeRegion G e (t+1))
    (hvw : G.Adj v w) : v ∈ edgeRegion G e t ∨ w ∈ edgeRegion G e t := by
  by_contra hn
  obtain ⟨hvn,hwn⟩ := not_or.mp hn
  let W := edgeRegion G e (t+1)
  let K : Set W := {x | x.val ∈ edgeRegion G e t}
  have hc : ((G.induce W).induce K).Connected :=
    connected_inside G (edgeRegion_step G e t) (edgeRegion_connected G e t)
  have hexp (x : V) (hx : x ∈ W) : (⟨x,hx⟩ : W) ∈ expand (G.induce W) K := by
    rcases hx with hx | ⟨y,hy,hxy⟩
    · exact Or.inl hx
    · exact Or.inr ⟨⟨y,edgeRegion_step G e t hy⟩,hy,hxy⟩
  exact outer_layer_independent (G.induce W) ht K hc (hexp v hv) (hexp w hw) hvn hwn hvw

theorem unique_neighbor_in_region (e : G.edgeSet) (t : ℕ)
    (ht : (G.induce (edgeRegion G e (t+1))).IsTree) {v w z : V}
    (hv : v ∉ edgeRegion G e t) (hw : w ∈ edgeRegion G e t)
    (hz : z ∈ edgeRegion G e t) (hvw : G.Adj v w) (hvz : G.Adj v z) : w = z := by
  have hvW : v ∈ edgeRegion G e (t+1) := Or.inr ⟨w,hw,hvw⟩
  have hc := connected_inside G (edgeRegion_step G e t) (edgeRegion_connected G e t)
  have he := unique_neighbor_into_connected_set (G.induce (edgeRegion G e (t+1))) ht
    {x | x.val ∈ edgeRegion G e t} hc (v := ⟨v,hvW⟩)
    (w := ⟨w,edgeRegion_step G e t hw⟩) (z := ⟨z,edgeRegion_step G e t hz⟩)
    hv hw hz hvw hvz
  exact congrArg Subtype.val he

end TreeGeometry
end
end MISLocal
