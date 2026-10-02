import MISLocal.AnonymousRule

/-! Anonymous rules inherit the concrete relabelings of regular tree
neighborhoods. The random private values are transported with their vertices;
their common distribution and the fair matrices make the transport invariant. -/

open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {Q : Type} [Fintype Q]

def orientationFlip {K L : Set V} (a : G.induce K ≃g G.induce L) (i : G.edgeSet) : Bool :=
  decide (regionPermutation G a (edgeLeft G i) ≠ edgeLeft G (edgePermutation G a i))

def anonymousInputRelabeling {K L : Set V} (a : G.induce K ≃g G.induce L)
    (R : FiniteProb Q) : InputRelabeling (matrixPrivateProbability G k (fun _ => R)) where
  coordinate := Equiv.sumCongr (edgePermutation G a) (regionPermutation G a)
  value i := match i with
    | Sum.inl i => matrixFlip k (orientationFlip G a i)
    | Sum.inr _ => Equiv.refl Q
  weight i x := by
    cases i with
    | inl i => rfl
    | inr v => rfl

theorem anonymousInput_raw {K L : Set V} (a : G.induce K ≃g G.induce L)
    (R : FiniteProb Q) (ω : ∀ i, matrixPrivateType G k (fun _ => Q) i) (i : G.edgeSet) :
    (anonymousInputRelabeling (k := k) G a R).input ω (Sum.inl (edgePermutation G a i)) =
      matrixFlip k (orientationFlip G a i) (ω (Sum.inl i)) := by
  exact Equiv.piCongr_apply_apply _ _ ω (Sum.inl i)

theorem anonymousInput_coin {K L : Set V} (a : G.induce K ≃g G.induce L)
    (R : FiniteProb Q) (ω : ∀ i, matrixPrivateType G k (fun _ => Q) i) (v : V) :
    (anonymousInputRelabeling (k := k) G a R).input ω (Sum.inr (regionPermutation G a v)) =
      ω (Sum.inr v) := by
  exact Equiv.piCongr_apply_apply _ _ ω (Sum.inr v)

omit [DecidableRel G.Adj] in
theorem orientation_datum {K L : Set V} (a : G.induce K ≃g G.induce L)
    {i : G.edgeSet} (hi : i ∈ internalEdges G K) (M : EdgeMatrix k) :
    (edgeLeft G (edgePermutation G a i),edgeRight G (edgePermutation G a i),
      matrixFlip k (orientationFlip G a i) M) =
    renameEdgeDatum (regionPermutation G a) (orientationFlip G a i)
      (edgeLeft G i,edgeRight G i,M) := by
  have hp := edgePermutation_val G a hi
  rw [← edge_endpoints G i, Sym2.map_pair_eq,
    ← edge_endpoints G (edgePermutation G a i)] at hp
  have hpair := Sym2.eq_iff.mp hp.symm
  rcases hpair with hpair | hpair
  · have hflip : orientationFlip G a i = false := by simp [orientationFlip, hpair.1]
    simp only [hflip, matrixFlip, Bool.false_eq_true, if_false, renameEdgeDatum,
      hpair.1, hpair.2]
    rfl
  · have hn : regionPermutation G a (edgeLeft G i) ≠ edgeLeft G (edgePermutation G a i) := by
      rw [hpair.1]
      exact (endpoint_adj G (edgePermutation G a i)).ne.symm
    have hflip : orientationFlip G a i = true := by simp [orientationFlip, hn]
    simp only [hflip, matrixFlip, if_true, renameEdgeDatum, hpair.1, hpair.2]
    rfl

theorem anonymous_view_renaming {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) (R : FiniteProb Q)
    (ω : ∀ i, matrixPrivateType G k (fun _ => Q) i) :
    LocalViewRenaming (namedLocalView G r (orientedRoot G e b) ω)
      (namedLocalView G r (orientedRoot G f c) ((anonymousInputRelabeling (k := k) G a.iso R).input ω)) := by
  refine ⟨regionPermutation G a.iso,edgePermutation G a.iso,orientationFlip G a.iso,
    (regionPermutation_root G a).symm,?_,?_⟩
  · change (anonymousInputRelabeling (k := k) G a.iso R).input ω (Sum.inr (orientedRoot G f c)) = _
    rw [← regionPermutation_root G a]
    exact anonymousInput_coin G a.iso R ω _
  · intro i
    have hs := edgePermutation_seen G a (Nat.le_refl r) i
    by_cases hi : i ∈ seen G r (orientedRoot G e b)
    · have ht := hs.mpr hi
      simp only [namedLocalView, ht, hi, if_true, Option.map_some]
      rw [anonymousInput_raw G a.iso R ω i]
      exact congrArg some (orientation_datum G a.iso (seen_internal G (Nat.le_refl r) hi) _)
    · have ht : edgePermutation G a.iso i ∉ seen G r (orientedRoot G f c) := fun h => hi (hs.mp h)
      simp only [namedLocalView, ht, hi, if_false, Option.map_none]
      rfl

theorem runAnonymous_transport {e f : G.edgeSet} {b c : Bool} {r : ℕ}
    (a : OrientedRegionIso G e f b c r) (R : FiniteProb Q)
    (A : AnonymousRule V G.edgeSet k Q) (ω : ∀ i, matrixPrivateType G k (fun _ => Q) i) :
    runAnonymous G A r (orientedRoot G f c) ((anonymousInputRelabeling (k := k) G a.iso R).input ω) =
      runAnonymous G A r (orientedRoot G e b) ω := by
  exact congrArg A (Quot.sound (anonymous_view_renaming G a R ω)).symm

theorem anonymous_coordinate_seen {e f : G.edgeSet} {b c : Bool} {r t : ℕ}
    (a : OrientedRegionIso G e f b c r) (R : FiniteProb Q) (ht : t ≤ r)
    (i : G.edgeSet ⊕ V) :
    (anonymousInputRelabeling (k := k) G a.iso R).coordinate i ∈
      rawView (V := V) (seen G t (orientedRoot G f c)) ↔
      i ∈ rawView (V := V) (seen G t (orientedRoot G e b)) := by
  cases i with
  | inl i => simpa [anonymousInputRelabeling, rawView] using edgePermutation_seen G a ht i
  | inr v => simp [anonymousInputRelabeling, rawView]

theorem anonymous_coordinate_shared {e f : G.edgeSet} {b c : Bool} {r t : ℕ}
    (a : OrientedRegionIso G e f b c r) (R : FiniteProb Q) (ht : t ≤ r)
    (i : G.edgeSet ⊕ V) :
    (anonymousInputRelabeling (k := k) G a.iso R).coordinate i ∈
      rawView (V := V) (sharedEdges G t f) ↔
      i ∈ rawView (V := V) (sharedEdges G t e) := by
  cases i with
  | inl i => simpa [anonymousInputRelabeling, rawView] using edgePermutation_shared G a ht i
  | inr v => simp [anonymousInputRelabeling, rawView]

/-- The symmetry used by the occupancy proof follows from the anonymous
rule definition and the regular tree neighborhoods. It is not a premise. -/
theorem anonymous_homogeneous {D r : ℕ}
    (hreg : ∀ v, G.degree v = D)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e r)).IsTree)
    (R : FiniteProb Q) (A : AnonymousRule V G.edgeSet k Q) :
    ViewHomogeneous (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R)))
      (runAnonymous G A r)
      (fun j v => observeInputs (rawView (V := V) (seen G (r-j) v)))
      (fun j e => observeInputs (rawView (V := V) (sharedEdges G (r-j) e)))
      (edgeLeft G) (edgeRight G) := by
  let iso := fun (s t : G.edgeSet × Bool) => regularRegionIso G hreg r ht s.1 t.1 s.2 t.2
  apply viewHomogeneous_of_input_relabelings _ _ _ _ _ _
    (fun s t => anonymousInputRelabeling (k := k) G (iso s t).iso R)
  · intro s t ω
    exact runAnonymous_transport G (iso s t) R A ω
  · intro s t ω
    exact runAnonymous_transport G ((iso s t).flip G) R A ω
  · intro s t j i
    exact anonymous_coordinate_seen (k := k) G (iso s t) R (Nat.sub_le r j) i
  · intro s t j i
    exact anonymous_coordinate_seen (k := k) G ((iso s t).flip G) R (Nat.sub_le r j) i
  · intro s t j i
    exact anonymous_coordinate_shared (k := k) G (iso s t) R (Nat.sub_le r j) i

end TreeGeometry
end
end MISLocal
