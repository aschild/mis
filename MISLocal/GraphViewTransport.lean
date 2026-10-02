import MISLocal.GraphNeighborhoodIso

/-! Extending a neighborhood isomorphism to permutations of the independent
input coordinates. All smaller round views are preserved. -/

open scoped Classical
namespace MISLocal
noncomputable section

theorem inBall_append {V : Type*} (G : SimpleGraph V) (t : ℕ) {v w u : V}
    (h : InBall G t v w) (ha : G.Adj w u) : InBall G (t+1) v u := by
  induction t generalizing v with
  | zero => subst w; exact Or.inr ⟨u,ha,rfl⟩
  | succ t ih =>
    rcases h with h | ⟨z,hvz,hzw⟩
    · subst w; exact Or.inr ⟨u,ha,inBall_self G (t+1) u⟩
    · exact Or.inr ⟨z,hvz,ih hzw⟩

theorem inBall_symm {V : Type*} (G : SimpleGraph V) (t : ℕ) {v w : V}
    (h : InBall G t v w) : InBall G t w v := by
  induction t generalizing v w with
  | zero => exact h.symm
  | succ t ih =>
    rcases h with h | ⟨z,hvz,hzw⟩
    · subst w; exact inBall_self G (t+1) v
    · exact inBall_append G t (ih hzw) hvz.symm

theorem inBall_mono {V : Type*} (G : SimpleGraph V) {s t : ℕ}
    (h : s ≤ t) {v w : V} : InBall G s v w → InBall G t v w := by
  induction h with
  | refl => exact id
  | @step t h ih => exact fun hv => inBall_mono_succ G t v w (ih hv)

namespace TreeGeometry
variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mem_edgeRegion_ball (e : G.edgeSet) (t : ℕ) (v : V) :
    v ∈ edgeRegion G e t ↔ ∃ w, w ∈ e.val ∧ InBall G t v w := by
  induction t generalizing v with
  | zero => simp only [edgeRegion, Set.mem_setOf_eq, InBall, exists_eq_right, and_true]
  | succ t ih =>
    constructor
    · rintro (hv | ⟨z,hz,hvz⟩)
      · obtain ⟨w,hw,hvw⟩ := (ih v).mp hv
        exact ⟨w,hw,inBall_mono_succ G t v w hvw⟩
      · obtain ⟨w,hw,hzw⟩ := (ih z).mp hz
        exact ⟨w,hw,Or.inr ⟨z,hvz,hzw⟩⟩
    · rintro ⟨w,hw,hvw | ⟨z,hvz,hzw⟩⟩
      · subst w; exact endpoint_mem_region G e (t+1) hw
      · exact Or.inr ⟨z,(ih z).mpr ⟨w,hw,hzw⟩,hvz⟩

omit [DecidableEq V] in
theorem seen_ball (s : ℕ) (v : V) (i : G.edgeSet) :
    i ∈ seen G (s+1) v ↔ ∃ w, w ∈ i.val ∧ InBall G s v w := by
  rw [mem_seen_succ, mem_edgeRegion_ball]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ball_in_region (e : G.edgeSet) {t : ℕ} {v w : V}
    (hv : v ∈ e.val) (h : InBall G t v w) : w ∈ edgeRegion G e t :=
  (mem_edgeRegion_ball G e t w).mpr ⟨v,hv,inBall_symm G t h⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem ball_region_add (e : G.edgeSet) {s t : ℕ} {v w : V}
    (hv : v ∈ edgeRegion G e s) (h : InBall G t v w) :
    w ∈ edgeRegion G e (s+t) := by
  induction t generalizing v s with
  | zero => simpa using h ▸ hv
  | succ t ih =>
    rcases h with h | ⟨z,hvz,hzw⟩
    · subst w; exact edgeRegion_mono G e (by omega) hv
    · have hz : z ∈ edgeRegion G e (s+1) := Or.inr ⟨v,hv,hvz.symm⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih hz hzw

def regionPermutation {K L : Set V} (f : G.induce K ≃g G.induce L) : V ≃ V :=
  f.toEquiv.extendSubtype

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem regionPermutation_mem {K L : Set V} (f : G.induce K ≃g G.induce L) (v : V) :
    regionPermutation G f v ∈ L ↔ v ∈ K := by
  by_cases hv : v ∈ K
  · exact iff_of_true (f.toEquiv.extendSubtype_mem v hv) hv
  · exact iff_of_false (f.toEquiv.extendSubtype_not_mem v hv) hv

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem regionPermutation_adj {K L : Set V} (f : G.induce K ≃g G.induce L)
    {v w : V} (hv : v ∈ K) (hw : w ∈ K) :
    G.Adj (regionPermutation G f v) (regionPermutation G f w) ↔ G.Adj v w := by
  rw [regionPermutation, f.toEquiv.extendSubtype_apply_of_mem v hv,
    f.toEquiv.extendSubtype_apply_of_mem w hw]
  exact f.map_rel_iff

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem regionPermutation_ball {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) {s t : ℕ} {v w : V}
    (hv : v ∈ edgeRegion G e s) (hst : s+t ≤ r) (h : InBall G t v w) :
    InBall G t (regionPermutation G a.iso v) (regionPermutation G a.iso w) := by
  induction t generalizing v s with
  | zero => exact congrArg (regionPermutation G a.iso) h
  | succ t ih =>
    rcases h with h | ⟨z,hvz,hzw⟩
    · exact Or.inl (congrArg (regionPermutation G a.iso) h)
    · have hz : z ∈ edgeRegion G e (s+1) := Or.inr ⟨v,hv,hvz.symm⟩
      exact Or.inr ⟨regionPermutation G a.iso z,
        (regionPermutation_adj G a.iso (edgeRegion_mono G e (by omega) hv)
          (edgeRegion_mono G e (by omega) hz)).mpr hvz,
        ih hz (by omega) hzw⟩

def internalEdges (K : Set V) : Set G.edgeSet := {e | ∀ v, v ∈ e.val → v ∈ K}

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem mapped_internal_edge {K L : Set V} (a : G.induce K ≃g G.induce L)
    (i : G.edgeSet) (hi : i ∈ internalEdges G K) :
    i.val.map (regionPermutation G a) ∈ G.edgeSet := by
  rw [← edge_endpoints G i, Sym2.map_pair_eq]
  exact (regionPermutation_adj G a
    (hi _ (orientedRoot_mem G i false)) (hi _ (orientedRoot_mem G i true))).mpr
    (endpoint_adj G i)

def internalEdgeMap {K L : Set V} (a : G.induce K ≃g G.induce L)
    (i : internalEdges G K) : internalEdges G L :=
  ⟨⟨i.val.val.map (regionPermutation G a),mapped_internal_edge G a i.val i.property⟩,by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
    exact (regionPermutation_mem G a w).mpr (i.property w hw)⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem internalEdgeMap_bijective {K L : Set V} (a : G.induce K ≃g G.induce L) :
    Function.Bijective (internalEdgeMap G a) := by
  let φ := regionPermutation G a
  have undo (z : Sym2 V) : (z.map φ).map φ.symm = z := by
    rw [Sym2.map_map]
    have h : (φ.symm : V → V) ∘ φ = id := funext φ.symm_apply_apply
    rw [h]
    exact congr_fun Sym2.map_id _
  constructor
  · intro i j h
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (Sym2.map φ.symm) (congrArg (fun z => z.val.val) h) |>.trans
      (undo j.val.val) |> fun he => (undo i.val.val).symm.trans he
  · intro j
    have hmem (v : V) : φ.symm v ∈ K ↔ v ∈ L := by
      simpa only [φ, Equiv.apply_symm_apply] using
        (regionPermutation_mem G a ((regionPermutation G a).symm v)).symm
    have ha : j.val.val.map φ.symm ∈ G.edgeSet := by
      rw [← edge_endpoints G j.val, Sym2.map_pair_eq]
      have hl := (hmem _).mpr (j.property _ (orientedRoot_mem G j.val false))
      have hr := (hmem _).mpr (j.property _ (orientedRoot_mem G j.val true))
      exact (regionPermutation_adj G a hl hr).mp (by simpa only [φ, Equiv.apply_symm_apply, orientedRoot, endpoint, Bool.false_eq_true, if_false, if_true] using endpoint_adj G j.val)
    let i : internalEdges G K := ⟨⟨j.val.val.map φ.symm,ha⟩,by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
      exact (hmem w).mpr (j.property w hw)⟩
    refine ⟨i,?_⟩
    apply Subtype.ext; apply Subtype.ext
    change (j.val.val.map φ.symm).map φ = j.val.val
    rw [Sym2.map_map]
    have h : (φ : V → V) ∘ φ.symm = id := funext φ.apply_symm_apply
    rw [h]
    exact congr_fun Sym2.map_id _

def internalEdgeEquiv {K L : Set V} (a : G.induce K ≃g G.induce L) :
    internalEdges G K ≃ internalEdges G L :=
  Equiv.ofBijective (internalEdgeMap G a) (internalEdgeMap_bijective G a)

def edgePermutation {K L : Set V} (a : G.induce K ≃g G.induce L) : G.edgeSet ≃ G.edgeSet :=
  (internalEdgeEquiv G a).extendSubtype

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem edgePermutation_val {K L : Set V} (a : G.induce K ≃g G.induce L)
    {i : G.edgeSet} (hi : i ∈ internalEdges G K) :
    (edgePermutation G a i).val = i.val.map (regionPermutation G a) := by
  rw [edgePermutation, Equiv.extendSubtype_apply_of_mem _ i hi]
  rfl

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem edgePermutation_internal {K L : Set V} (a : G.induce K ≃g G.induce L)
    (i : G.edgeSet) : edgePermutation G a i ∈ internalEdges G L ↔ i ∈ internalEdges G K := by
  by_cases hi : i ∈ internalEdges G K
  · exact iff_of_true ((internalEdgeEquiv G a).extendSubtype_mem i hi) hi
  · exact iff_of_false ((internalEdgeEquiv G a).extendSubtype_not_mem i hi) hi

def OrientedRegionIso.symm {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) : OrientedRegionIso G f e c b r where
  iso := a.iso.symm
  first := by
    have h : a.iso ⟨orientedRoot G e b,endpoint_mem_region G e r (orientedRoot_mem G e b)⟩ =
        ⟨orientedRoot G f c,endpoint_mem_region G f r (orientedRoot_mem G f c)⟩ :=
      Subtype.ext a.first
    exact congrArg Subtype.val (a.iso.symm_apply_eq.mpr h.symm)
  second := by
    have h : a.iso ⟨orientedRoot G e (!b),endpoint_mem_region G e r (orientedRoot_mem G e (!b))⟩ =
        ⟨orientedRoot G f (!c),endpoint_mem_region G f r (orientedRoot_mem G f (!c))⟩ :=
      Subtype.ext a.second
    exact congrArg Subtype.val (a.iso.symm_apply_eq.mpr h.symm)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem regionPermutation_inverse {K L : Set V} (a : G.induce K ≃g G.induce L)
    {v : V} (hv : v ∈ K) :
    regionPermutation G a.symm (regionPermutation G a v) = v := by
  change a.symm.toEquiv.extendSubtype (a.toEquiv.extendSubtype v) = v
  rw [a.toEquiv.extendSubtype_apply_of_mem v hv]
  change a.symm.toEquiv.extendSubtype (a ⟨v,hv⟩).val = v
  rw [a.symm.toEquiv.extendSubtype_apply_of_mem _ (a ⟨v,hv⟩).property]
  exact congrArg Subtype.val (a.symm_apply_apply ⟨v,hv⟩)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem regionPermutation_root {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) :
    regionPermutation G a.iso (orientedRoot G e b) = orientedRoot G f c := by
  rw [regionPermutation, a.iso.toEquiv.extendSubtype_apply_of_mem _
    (endpoint_mem_region G e r (orientedRoot_mem G e b))]
  exact a.first

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem regionPermutation_other {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) :
    regionPermutation G a.iso (orientedRoot G e (!b)) = orientedRoot G f (!c) := by
  rw [regionPermutation, a.iso.toEquiv.extendSubtype_apply_of_mem _
    (endpoint_mem_region G e r (orientedRoot_mem G e (!b)))]
  exact a.second

def OrientedRegionIso.flip {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) : OrientedRegionIso G e f (!b) (!c) r :=
  ⟨a.iso,a.second,by simpa only [Bool.not_not] using a.first⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem regionPermutation_root_ball {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) {t : ℕ} (ht : t ≤ r)
    {w : V} (hw : w ∈ edgeRegion G e r) :
    InBall G t (orientedRoot G f c) (regionPermutation G a.iso w) ↔
      InBall G t (orientedRoot G e b) w := by
  constructor
  · intro h
    have h' := regionPermutation_ball G (a.symm G)
      (s := 0) (orientedRoot_mem G f c) (by omega) h
    rw [regionPermutation_root G (a.symm G)] at h'
    change InBall G t (orientedRoot G e b)
      (regionPermutation G a.iso.symm (regionPermutation G a.iso w)) at h'
    rw [regionPermutation_inverse G a.iso hw] at h'
    exact h'
  · intro h
    have h' := regionPermutation_ball G a (s := 0) (orientedRoot_mem G e b) (by omega) h
    rwa [regionPermutation_root G a] at h'

omit [DecidableEq V] in
theorem seen_internal {e : G.edgeSet} {b : Bool} {r t : ℕ} (ht : t ≤ r)
    {i : G.edgeSet} (hi : i ∈ seen G t (orientedRoot G e b)) :
    i ∈ internalEdges G (edgeRegion G e r) := by
  cases t with
  | zero => exact False.elim (Finset.not_mem_empty i hi)
  | succ t =>
    obtain ⟨w,hw,hball⟩ := (seen_ball G t _ i).mp hi
    intro v hv
    have hvball : InBall G (t+1) (orientedRoot G e b) v := by
      rw [← edge_endpoints G i, Sym2.mem_iff] at hw hv
      rcases hw with hw | hw <;> rcases hv with hv | hv
      · exact inBall_mono_succ G t _ _ (hv.symm ▸ hw ▸ hball)
      · exact inBall_append G t (hw ▸ hball) (hv.symm ▸ endpoint_adj G i)
      · exact inBall_append G t (hw ▸ hball) (hv.symm ▸ (endpoint_adj G i).symm)
      · exact inBall_mono_succ G t _ _ (hv.symm ▸ hw ▸ hball)
    exact edgeRegion_mono G e ht (ball_in_region G e (orientedRoot_mem G e b) hvball)

omit [DecidableEq V] in
theorem edgePermutation_seen {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) {t : ℕ} (ht : t ≤ r) (i : G.edgeSet) :
    edgePermutation G a.iso i ∈ seen G t (orientedRoot G f c) ↔
      i ∈ seen G t (orientedRoot G e b) := by
  cases t with
  | zero => simp [seen]
  | succ t =>
    constructor
    · intro hi
      have hiK := (edgePermutation_internal G a.iso i).mp (seen_internal G ht hi)
      obtain ⟨w,hw,hball⟩ := (seen_ball G t _ _).mp hi
      rw [edgePermutation_val G a.iso hiK] at hw
      obtain ⟨z,hz,rfl⟩ := Sym2.mem_map.mp hw
      exact (seen_ball G t _ i).mpr ⟨z,hz,
        (regionPermutation_root_ball G a (by omega) (hiK z hz)).mp hball⟩
    · intro hi
      have hiK := seen_internal G ht hi
      obtain ⟨w,hw,hball⟩ := (seen_ball G t _ i).mp hi
      exact (seen_ball G t _ _).mpr ⟨regionPermutation G a.iso w,
        by rw [edgePermutation_val G a.iso hiK]; exact Sym2.mem_map.mpr ⟨w,hw,rfl⟩,
        (regionPermutation_root_ball G a (by omega) (hiK w hw)).mpr hball⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem edgePermutation_center {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) : edgePermutation G a.iso e = f := by
  apply Subtype.ext
  rw [edgePermutation_val G a.iso (fun v hv => endpoint_mem_region G e r hv)]
  have hp : e.val = s(orientedRoot G e b,orientedRoot G e (!b)) := by
    cases b <;> simp only [orientedRoot, endpoint, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true]
    · exact (edge_endpoints G e).symm
    · exact (edge_endpoints G e).symm.trans Sym2.eq_swap
  rw [hp, Sym2.map_pair_eq, regionPermutation_root G a, regionPermutation_other G a]
  cases c <;> simp only [orientedRoot, endpoint, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, if_false, if_true]
  · exact edge_endpoints G f
  · exact Sym2.eq_swap.trans (edge_endpoints G f)

theorem edgePermutation_shared {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) {t : ℕ} (ht : t ≤ r) (i : G.edgeSet) :
    edgePermutation G a.iso i ∈ sharedEdges G t f ↔ i ∈ sharedEdges G t e := by
  have heq : edgePermutation G a.iso i = f ↔ i = e := by
    constructor
    · intro h
      exact (edgePermutation G a.iso).injective (h.trans (edgePermutation_center G a).symm)
    · intro h; subst i; exact edgePermutation_center G a
  have h1 := edgePermutation_seen G a ht i
  have h2 := edgePermutation_seen G (a.flip G) ht i
  rw [mem_sharedEdges, mem_sharedEdges]
  cases b <;> cases c <;>
    simp only [orientedRoot, endpoint, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] at h1 h2 <;> tauto

end TreeGeometry
end
end MISLocal
