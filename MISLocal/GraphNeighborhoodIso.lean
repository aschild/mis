import MISLocal.GraphInputGeometry
import MISLocal.Locality
import Mathlib.Logic.Equiv.Fintype

/-! Isomorphisms of finite regular tree neighborhoods. The isomorphisms
are constructed by matching the children of each vertex, not assumed. -/

open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev OutsideNeighbor (K : Set V) (v : K) := {w : V // G.Adj v.val w ∧ w ∉ K}

def neighborSplit (K : Set V) (v : K) :
    G.neighborSet v.val ≃ (G.induce K).neighborSet v ⊕ OutsideNeighbor G K v where
  toFun w := if h : w.val ∈ K then Sum.inl ⟨⟨w.val,h⟩,w.property⟩
    else Sum.inr ⟨w.val,w.property,h⟩
  invFun w := match w with
    | Sum.inl w => ⟨w.val.val,w.property⟩
    | Sum.inr w => ⟨w.val,w.property.1⟩
  left_inv w := by by_cases h : w.val ∈ K <;> simp only [h, dite_true, dite_false]
  right_inv w := by cases w with
    | inl w => simp only [w.val.property, dite_true]
    | inr w => simp only [w.property.2, dite_false]

omit [DecidableEq V] in
theorem outside_card {K L : Set V} (f : G.induce K ≃g G.induce L)
    {D : ℕ} (hreg : ∀ v, G.degree v = D) (v : K) :
    Fintype.card (OutsideNeighbor G K v) = Fintype.card (OutsideNeighbor G L (f v)) := by
  have hK := Fintype.card_congr (neighborSplit G K v)
  have hL := Fintype.card_congr (neighborSplit G L (f v))
  have hi := Fintype.card_congr (f.mapNeighborSet v)
  rw [Fintype.card_sum, G.card_neighborSet_eq_degree, hreg] at hK hL
  omega

abbrev ExpandCode (K : Set V) := K ⊕ Σ v : K, OutsideNeighbor G K v

def expandDecode (K : Set V) : ExpandCode G K → expand G K
  | Sum.inl v => ⟨v.val,Or.inl v.property⟩
  | Sum.inr ⟨v,w⟩ => ⟨w.val,Or.inr ⟨v.val,v.property,w.property.1.symm⟩⟩

theorem expandDecode_bijective (K : Set V)
    (ht : (G.induce (expand G K)).IsTree) (hc : (G.induce K).Connected) :
    Function.Bijective (expandDecode G K) := by
  have uniq {x a b : V} (hx : x ∉ K) (ha : a ∈ K) (hb : b ∈ K)
      (hxa : G.Adj x a) (hxb : G.Adj x b) : a = b := by
    have hxW : x ∈ expand G K := Or.inr ⟨a,ha,hxa⟩
    exact congrArg Subtype.val (unique_neighbor_into_connected_set
      (G.induce (expand G K)) ht {v | v.val ∈ K}
      (connected_inside G (subset_expand G K) hc)
      (v := ⟨x,hxW⟩) (w := ⟨a,Or.inl ha⟩) (z := ⟨b,Or.inl hb⟩)
      hx ha hb hxa hxb)
  constructor
  · intro a b hab
    have hv := congrArg Subtype.val hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hv)
      | inr b => exact False.elim (b.2.property.2 (hv ▸ a.property))
    | inr a =>
      cases b with
      | inl b => exact False.elim (a.2.property.2 (hv.symm ▸ b.property))
      | inr b =>
        have hp : a.1 = b.1 := Subtype.ext
          (uniq a.2.property.2 a.1.property b.1.property
            a.2.property.1.symm (hv.symm ▸ b.2.property.1.symm))
        obtain ⟨a,w⟩ := a
        obtain ⟨b,z⟩ := b
        dsimp at hp
        subst b
        exact congrArg Sum.inr (congrArg (Sigma.mk a) (Subtype.ext hv))
  · rintro ⟨v,hv⟩
    rcases hv with hv | ⟨w,hw,hvw⟩
    · exact ⟨Sum.inl ⟨v,hv⟩,rfl⟩
    · by_cases h : v ∈ K
      · exact ⟨Sum.inl ⟨v,h⟩,rfl⟩
      · exact ⟨Sum.inr ⟨⟨w,hw⟩,⟨v,hvw.symm,h⟩⟩,rfl⟩

def expandCodeEquiv (K : Set V) (ht : (G.induce (expand G K)).IsTree)
    (hc : (G.induce K).Connected) : ExpandCode G K ≃ expand G K :=
  Equiv.ofBijective (expandDecode G K) (expandDecode_bijective G K ht hc)

theorem expand_adj_code (K : Set V) (ht : (G.induce (expand G K)).IsTree)
    (hc : (G.induce K).Connected) (a b : ExpandCode G K) :
    G.Adj (expandDecode G K a).val (expandDecode G K b).val ↔
    match a,b with
    | Sum.inl v,Sum.inl w => G.Adj v.val w.val
    | Sum.inl v,Sum.inr w => v = w.1
    | Sum.inr v,Sum.inl w => v.1 = w
    | Sum.inr _,Sum.inr _ => False := by
  have uniq {x a b : V} (hx : x ∉ K) (ha : a ∈ K) (hb : b ∈ K)
      (hxa : G.Adj x a) (hxb : G.Adj x b) : a = b := by
    exact congrArg Subtype.val (unique_neighbor_into_connected_set
      (G.induce (expand G K)) ht {v | v.val ∈ K}
      (connected_inside G (subset_expand G K) hc)
      (v := ⟨x,Or.inr ⟨a,ha,hxa⟩⟩) (w := ⟨a,Or.inl ha⟩) (z := ⟨b,Or.inl hb⟩)
      hx ha hb hxa hxb)
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b =>
      constructor
      · intro h
        exact Subtype.ext (uniq b.2.property.2 a.property b.1.property h.symm
          b.2.property.1.symm)
      · intro h; subst a; exact b.2.property.1
  | inr a =>
    cases b with
    | inl b =>
      constructor
      · intro h
        exact Subtype.ext (uniq a.2.property.2 a.1.property b.property
          a.2.property.1.symm h)
      · intro h; subst b; exact a.2.property.1.symm
    | inr b =>
      exact iff_false_intro (outer_layer_independent (G.induce (expand G K)) ht
        {v | v.val ∈ K} (connected_inside G (subset_expand G K) hc)
        (v := expandDecode G K (Sum.inr a)) (w := expandDecode G K (Sum.inr b))
        (Or.inr ⟨⟨a.1.val,Or.inl a.1.property⟩,a.1.property,a.2.property.1.symm⟩)
        (Or.inr ⟨⟨b.1.val,Or.inl b.1.property⟩,b.1.property,b.2.property.1.symm⟩)
        a.2.property.2 b.2.property.2)

def expandIso {K L : Set V} (f : G.induce K ≃g G.induce L)
    {D : ℕ} (hreg : ∀ v, G.degree v = D)
    (hK : (G.induce (expand G K)).IsTree) (hL : (G.induce (expand G L)).IsTree)
    (hcK : (G.induce K).Connected) (hcL : (G.induce L).Connected) :
    G.induce (expand G K) ≃g G.induce (expand G L) := by
  let child := fun v => Fintype.equivOfCardEq (outside_card G f hreg v)
  let c := Equiv.sumCongr f.toEquiv (Equiv.sigmaCongr f.toEquiv child)
  let a := expandCodeEquiv G K hK hcK
  let b := expandCodeEquiv G L hL hcL
  refine { toEquiv := a.symm.trans (c.trans b), map_rel_iff' := ?_ }
  intro v w
  obtain ⟨v,rfl⟩ := a.surjective v
  obtain ⟨w,rfl⟩ := a.surjective w
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  change G.Adj (b (c v)).val (b (c w)).val ↔ G.Adj (a v).val (a w).val
  rw [show (a v).val = (expandDecode G K v).val from rfl,
    show (a w).val = (expandDecode G K w).val from rfl,
    show (b (c v)).val = (expandDecode G L (c v)).val from rfl,
    show (b (c w)).val = (expandDecode G L (c w)).val from rfl]
  rw [expand_adj_code G L hL hcL, expand_adj_code G K hK hcK]
  cases v with
  | inl v =>
    cases w with
    | inl w => exact f.map_rel_iff
    | inr w => simp [c, Equiv.sigmaCongr, Equiv.sigmaCongrLeft]
  | inr v =>
    cases w with
    | inl w => simp [c, Equiv.sigmaCongr, Equiv.sigmaCongrLeft]
    | inr w => rfl

theorem expandIso_old {K L : Set V} (f : G.induce K ≃g G.induce L)
    {D : ℕ} (hreg : ∀ v, G.degree v = D)
    (hK : (G.induce (expand G K)).IsTree) (hL : (G.induce (expand G L)).IsTree)
    (hcK : (G.induce K).Connected) (hcL : (G.induce L).Connected) (v : K) :
    (expandIso G f hreg hK hL hcK hcL ⟨v.val,Or.inl v.property⟩).val = (f v).val := by
  have h := (expandCodeEquiv G K hK hcK).symm_apply_apply (Sum.inl v)
  change (expandCodeEquiv G K hK hcK).symm ⟨v.val,Or.inl v.property⟩ = Sum.inl v at h
  change (expandCodeEquiv G L hL hcL
    ((Equiv.sumCongr f.toEquiv (Equiv.sigmaCongr f.toEquiv
      (fun v => Fintype.equivOfCardEq (outside_card G f hreg v))))
      ((expandCodeEquiv G K hK hcK).symm ⟨v.val,Or.inl v.property⟩))).val = _
  rw [h]
  rfl

def orientedRoot (e : G.edgeSet) (b : Bool) : V :=
  endpoint (edgeLeft G) (edgeRight G) e b

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem orientedRoot_mem (e : G.edgeSet) (b : Bool) : orientedRoot G e b ∈ e.val := by
  rw [← edge_endpoints G e]
  cases b <;> simp [orientedRoot, endpoint]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem orientedRoot_adj (e : G.edgeSet) (b : Bool) :
    G.Adj (orientedRoot G e b) (orientedRoot G e (!b)) := by
  cases b
  · exact endpoint_adj G e
  · exact (endpoint_adj G e).symm

def pairCode (e : G.edgeSet) (b : Bool) : Bool ≃ edgeRegion G e 0 :=
  Equiv.ofBijective (fun q =>
    ⟨orientedRoot G e (if q then !b else b),orientedRoot_mem G e _⟩) (by
      constructor
      · intro q p h
        have hv := congrArg Subtype.val h
        cases q <;> cases p
        · rfl
        · exact False.elim ((orientedRoot_adj G e b).ne hv)
        · exact False.elim ((orientedRoot_adj G e b).ne hv.symm)
        · rfl
      · rintro ⟨v,hv⟩
        change v ∈ e.val at hv
        rw [← edge_endpoints G e, Sym2.mem_iff] at hv
        cases b <;> rcases hv with hv | hv <;> subst v
        · exact ⟨false,rfl⟩
        · exact ⟨true,rfl⟩
        · exact ⟨true,rfl⟩
        · exact ⟨false,rfl⟩)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem pairCode_adj (e : G.edgeSet) (b q p : Bool) :
    G.Adj (pairCode G e b q).val (pairCode G e b p).val ↔ q ≠ p := by
  cases q <;> cases p <;> simp [pairCode, orientedRoot_adj, (orientedRoot_adj G e b).symm]

def pairIso (e f : G.edgeSet) (b c : Bool) :
    G.induce (edgeRegion G e 0) ≃g G.induce (edgeRegion G f 0) where
  toEquiv := (pairCode G e b).symm.trans (pairCode G f c)
  map_rel_iff' := by
    intro v w
    obtain ⟨q,rfl⟩ := (pairCode G e b).surjective v
    obtain ⟨p,rfl⟩ := (pairCode G e b).surjective w
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    change G.Adj (pairCode G f c q).val (pairCode G f c p).val ↔
      G.Adj (pairCode G e b q).val (pairCode G e b p).val
    rw [pairCode_adj, pairCode_adj]

structure OrientedRegionIso (e f : G.edgeSet) (b c : Bool) (r : ℕ) where
  iso : G.induce (edgeRegion G e r) ≃g G.induce (edgeRegion G f r)
  first : (iso ⟨orientedRoot G e b,endpoint_mem_region G e r (orientedRoot_mem G e b)⟩).val =
    orientedRoot G f c
  second : (iso ⟨orientedRoot G e (!b),endpoint_mem_region G e r (orientedRoot_mem G e (!b))⟩).val =
    orientedRoot G f (!c)

def regularRegionIso {D : ℕ} (hreg : ∀ v, G.degree v = D)
    (r : ℕ) (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e r)).IsTree)
    (e f : G.edgeSet) (b c : Bool) : OrientedRegionIso G e f b c r := by
  induction r with
  | zero =>
    refine ⟨pairIso G e f b c,?_,?_⟩
    · have h := (pairCode G e b).symm_apply_apply false
      change (pairCode G e b).symm
        ⟨orientedRoot G e b,orientedRoot_mem G e b⟩ = false at h
      change ((pairCode G f c) ((pairCode G e b).symm _)).val = _
      rw [h]; rfl
    · have h := (pairCode G e b).symm_apply_apply true
      change (pairCode G e b).symm
        ⟨orientedRoot G e (!b),orientedRoot_mem G e (!b)⟩ = true at h
      change ((pairCode G f c) ((pairCode G e b).symm _)).val = _
      rw [h]; rfl
  | succ r ih =>
    let prev := ih (fun e => induced_region_tree G e (Nat.le_succ r) (ht e))
    let next := expandIso G prev.iso hreg (ht e) (ht f)
      (edgeRegion_connected G e r) (edgeRegion_connected G f r)
    refine ⟨next,?_,?_⟩
    · exact (expandIso_old G prev.iso hreg (ht e) (ht f)
        (edgeRegion_connected G e r) (edgeRegion_connected G f r) _).trans prev.first
    · exact (expandIso_old G prev.iso hreg (ht e) (ht f)
        (edgeRegion_connected G e r) (edgeRegion_connected G f r) _).trans prev.second

end TreeGeometry
end
end MISLocal
