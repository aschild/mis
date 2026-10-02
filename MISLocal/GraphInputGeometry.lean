import MISLocal.GraphBalls
import MISLocal.InputGeometry
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Construct the independent-input geometry from actual finite, regular,
locally tree-like graphs. `seen s v` consists of edge inputs reached in `s`
rounds: no edges in round zero, incident edges in round one, and one further
neighbor expansion per round. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

def seen : ℕ → V → Finset G.edgeSet
  | 0, _ => ∅
  | t+1, v => Finset.univ.filter (fun e => v ∈ edgeRegion G e t)

omit [DecidableEq V] in
@[simp] theorem mem_seen_succ (s : ℕ) (v : V) (e : G.edgeSet) :
    e ∈ seen G (s+1) v ↔ v ∈ edgeRegion G e s := by simp [seen]

theorem seen_mono {s t : ℕ} (hst : s ≤ t) (v : V) : seen G s v ⊆ seen G t v := by
  cases s with
  | zero => exact Finset.empty_subset _
  | succ s =>
    cases t with
    | zero => omega
    | succ t =>
      intro e he
      exact (mem_seen_succ G t v e).mpr
        (edgeRegion_mono G e (by omega) ((mem_seen_succ G s v e).mp he))

def sharedEdges (s : ℕ) (e : G.edgeSet) : Finset G.edgeSet :=
  insert e (seen G s (edgeLeft G e) ∪ seen G s (edgeRight G e))

@[simp] theorem mem_sharedEdges (s : ℕ) (e i : G.edgeSet) :
    i ∈ sharedEdges G s e ↔ i = e ∨ i ∈ seen G s (edgeLeft G e) ∨
      i ∈ seen G s (edgeRight G e) := by simp [sharedEdges]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem endpoint_adj (e : G.edgeSet) : G.Adj (edgeLeft G e) (edgeRight G e) := by
  have h := e.property
  rw [← edge_endpoints G e] at h
  exact h

theorem seen_into_shared (s : ℕ) (v : V) (e : G.edgeSet)
    (hv : edgeIncident (edgeLeft G) (edgeRight G) v e) :
    seen G s v ⊆ sharedEdges G s e := by
  intro i hi
  rcases hv with hv | hv
  · exact (mem_sharedEdges G s e i).mpr (Or.inr (Or.inl (hv ▸ hi)))
  · exact (mem_sharedEdges G s e i).mpr (Or.inr (Or.inr (hv ▸ hi)))

omit [DecidableEq V] in
theorem seen_neighbor {s : ℕ} {v w : V} (hvw : G.Adj v w) :
    seen G s w ⊆ seen G (s+1) v := by
  cases s with
  | zero => exact Finset.empty_subset _
  | succ s =>
    intro i hi
    exact (mem_seen_succ G (s+1) v i).mpr
      (Or.inr ⟨w,(mem_seen_succ G s w i).mp hi,hvw⟩)

theorem shared_inside_seen (s : ℕ) (v : V) (e : G.edgeSet)
    (hv : edgeIncident (edgeLeft G) (edgeRight G) v e) :
    sharedEdges G s e ⊆ seen G (s+1) v := by
  intro i hi
  rcases (mem_sharedEdges G s e i).mp hi with he | hl | hr
  · subst i
    exact (mem_seen_succ G s v e).mpr
      (endpoint_mem_region G e s ((incident_iff_mem G v e).mp hv))
  · rcases hv with hv | hv
    · exact seen_mono G (Nat.le_succ s) v (hv ▸ hl)
    · exact seen_neighbor G (hv ▸ (endpoint_adj G e).symm) hl
  · rcases hv with hv | hv
    · exact seen_neighbor G (hv ▸ endpoint_adj G e) hr
    · exact seen_mono G (Nat.le_succ s) v (hv ▸ hr)

theorem seen_endpoint_overlap (s : ℕ) (e : G.edgeSet)
    (ht : ∀ i : G.edgeSet, (G.induce (edgeRegion G i s)).IsTree) :
    seen G (s+1) (edgeLeft G e) ∩ seen G (s+1) (edgeRight G e) ⊆ sharedEdges G s e := by
  intro i hi
  obtain ⟨hl,hr⟩ := Finset.mem_inter.mp hi
  have hl' := (mem_seen_succ G s _ i).mp hl
  have hr' := (mem_seen_succ G s _ i).mp hr
  cases s with
  | zero =>
    have he := edge_eq_of_incident G (endpoint_adj G e).ne i
      ((incident_iff_mem G _ i).mpr hl') ((incident_iff_mem G _ i).mpr hr')
    exact (mem_sharedEdges G 0 e i).mpr (Or.inl (Subtype.ext (he.trans (edge_endpoints G e))))
  | succ s =>
    rcases adjacent_region_step G i s (ht i) hl' hr' (endpoint_adj G e) with hl | hr
    · exact (mem_sharedEdges G (s+1) e i).mpr
        (Or.inr (Or.inl ((mem_seen_succ G s _ i).mpr hl)))
    · exact (mem_sharedEdges G (s+1) e i).mpr
        (Or.inr (Or.inr ((mem_seen_succ G s _ i).mpr hr)))

theorem shared_branch_overlap (s : ℕ) (v : V) (e f : G.edgeSet) (hef : e ≠ f)
    (hve : edgeIncident (edgeLeft G) (edgeRight G) v e)
    (hvf : edgeIncident (edgeLeft G) (edgeRight G) v f)
    (ht : ∀ i : G.edgeSet, (G.induce (edgeRegion G i s)).IsTree) :
    sharedEdges G s e ∩ sharedEdges G s f ⊆ seen G s v := by
  intro i hi
  obtain ⟨he,hf⟩ := Finset.mem_inter.mp hi
  cases s with
  | zero =>
    have heq : i = e := by simpa [sharedEdges, seen] using he
    have hfq : i = f := by simpa [sharedEdges, seen] using hf
    exact False.elim (hef (heq.symm.trans hfq))
  | succ s =>
    by_contra hn
    have hvn : v ∉ edgeRegion G i s := fun h => hn ((mem_seen_succ G s v i).mpr h)
    have enters (a : G.edgeSet) (hva : edgeIncident (edgeLeft G) (edgeRight G) v a)
        (ha : i ∈ sharedEdges G (s+1) a) :
        ∃ w, w ∈ edgeRegion G i s ∧ G.Adj v w ∧ a.val = s(v,w) := by
      rcases (mem_sharedEdges G (s+1) a i).mp ha with hia | hl | hr
      · subst a
        exact False.elim (hvn (endpoint_mem_region G i s ((incident_iff_mem G v i).mp hva)))
      · have hw := (mem_seen_succ G s _ i).mp hl
        have hne : v ≠ edgeLeft G a := fun h => hvn (h ▸ hw)
        have hae := edge_eq_of_incident G hne a hva (Or.inl rfl)
        exact ⟨edgeLeft G a,hw,by simpa only [hae] using a.property,hae⟩
      · have hw := (mem_seen_succ G s _ i).mp hr
        have hne : v ≠ edgeRight G a := fun h => hvn (h ▸ hw)
        have hae := edge_eq_of_incident G hne a hva (Or.inr rfl)
        exact ⟨edgeRight G a,hw,by simpa only [hae] using a.property,hae⟩
    obtain ⟨w,hw,hvw,heq⟩ := enters e hve he
    obtain ⟨z,hz,hvz,hfq⟩ := enters f hvf hf
    have hwz := unique_neighbor_in_region G i s (ht i) hvn hw hz hvw hvz
    exact hef (Subtype.ext (heq.trans (by rw [hwz, hfq])))

theorem incident_card_eq_degree (v : V) :
    (Finset.univ.filter (edgeIncident (edgeLeft G) (edgeRight G) v)).card = G.degree v := by
  let f : {e : G.edgeSet // edgeIncident (edgeLeft G) (edgeRight G) v e} ≃ G.incidenceSet v :=
    { toFun := fun e => ⟨e.val.val,e.val.property,(incident_iff_mem G v e.val).mp e.property⟩
      invFun := fun e => ⟨⟨e.val,e.property.1⟩,(incident_iff_mem G v _).mpr e.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr f, G.card_incidenceSet_eq_degree]

omit [DecidableEq V] in
theorem regular_edge_count (d : ℕ) (hreg : ∀ v, G.degree v = d+1) :
    2*Fintype.card G.edgeSet = (d+1)*Fintype.card V := by
  have h := G.sum_degrees_eq_twice_card_edges
  simp only [hreg, Finset.sum_const, Finset.card_univ, smul_eq_mul, G.edgeFinset_card] at h
  simpa only [Nat.mul_comm] using h.symm

/-- The outward source routes are constructed from parent edges in the
actual reader trees. `s = 0` is handled separately; no negative radius is
encoded by silently truncated subtraction. -/
def graphSourceCharge (d n s : ℕ) (hs : s ≤ n+1)
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree) :
    SourceCharge (edgeLeft G) (edgeRight G) (seen G (n+1)) (seen G s)
      (sharedEdges G s) d := by
  let root : ∀ i : G.edgeSet, {v // i ∈ seen G (n+1) v} := fun i =>
    ⟨edgeLeft G i,(mem_seen_succ G n _ i).mpr (endpoint_mem_region G i n
      ((incident_iff_mem G _ i).mp (Or.inl rfl)))⟩
  apply sourceChargeOfReaderTrees G (seen G (n+1)) (seen G s) (sharedEdges G s) d
    root (fun i => i)
  · intro i
    have hset : {v | i ∈ seen G (n+1) v} = edgeRegion G i n :=
      Set.ext (fun v => mem_seen_succ G n v i)
    rw [hset]
    exact induced_region_tree G i (Nat.le_succ n) (ht i)
  · intro i
    exact (incident_iff_mem G _ i).mp (Or.inl rfl)
  · intro v
    rw [incident_card_eq_degree G v, hreg v]
  · exact seen_mono G hs
  · intro i v hv
    cases s with
    | zero => exact False.elim (Finset.not_mem_empty i hv)
    | succ s =>
      constructor
      · exact (mem_seen_succ G s _ i).mpr (endpoint_mem_region G i s
          ((incident_iff_mem G _ i).mp (Or.inl rfl)))
      · have hc := connected_inside G (edgeRegion_mono G i (show s ≤ n by omega))
          (edgeRegion_connected G i s)
        have hsets (t : ℕ) : {v | i ∈ seen G (t+1) v} = edgeRegion G i t :=
          Set.ext (fun v => mem_seen_succ G t v i)
        change ((G.induce {v | i ∈ seen G (n+1) v}).induce
          {w | w.val ∈ {v | i ∈ seen G (s+1) v}}).Connected
        rw [hsets n, hsets s]
        exact hc
  · intro i e hi
    rcases (mem_sharedEdges G s e i).mp hi with he | hl | hr
    · exact Or.inr (Or.inr he.symm)
    · exact Or.inl hl
    · exact Or.inr (Or.inl hr)
  · exact seen_into_shared G s

/-- All overlap, independence-routing, and incidence premises of the finite
occupancy theorem follow from regularity and acyclicity of the displayed
edge-centered neighborhoods. The only subtraction is the layer-to-radius
conversion; every use requiring positivity proves it from `j < n+1`. -/
def graphInputGeometry (d n : ℕ) (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree) :
    ProductInputGeometry G.edgeSet V G.edgeSet d (n+1) where
  left := edgeLeft G
  right := edgeRight G
  noLoop := fun e => (endpoint_adj G e).ne.symm
  degree := fun v => (incident_card_eq_degree G v).trans (hreg v)
  edgeCount := regular_edge_count G d hreg
  readers := seen G (n+1)
  vertex := fun j => seen G (n+1-j)
  shared := fun j => sharedEdges G (n+1-j)
  vertex_readers := fun j v _ => seen_mono G (Nat.sub_le _ _) v
  nested := fun j v _ => seen_mono G (by omega) v
  empty_last := fun v => by simp [seen]
  contains := fun j v e _ => seen_into_shared G (n+1-j) v e
  shared_inside := by
    intro j v e hj hve
    have he : n+1-j = (n+1-(j+1))+1 := by omega
    rw [he]
    exact shared_inside_seen G _ v e hve
  endpoint_overlap := by
    intro j e hj
    have he : n+1-j = (n+1-(j+1))+1 := by omega
    rw [he]
    exact seen_endpoint_overlap G _ e (fun i => induced_region_tree G i (by omega) (ht i))
  branch_overlap := fun j v e f _ hef hve hvf => shared_branch_overlap G _ v e f hef hve hvf
    (fun i => induced_region_tree G i (Nat.sub_le _ _) (ht i))
  initial_reader_overlap := by
    intro e i hi
    exact seen_into_shared G (n+1) _ e (Or.inl rfl) (Finset.mem_inter.mp hi).1
  initial_shared_overlap := fun _ _ _ _ hi => (Finset.mem_inter.mp hi).1
  charge := fun j _ => graphSourceCharge G d n (n+1-j) (Nat.sub_le _ _) hreg ht

end TreeGeometry
end
end MISLocal
