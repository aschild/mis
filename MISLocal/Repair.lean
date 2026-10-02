import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-!
# Deterministic graph facts used by the LOCAL reduction

These are statements about Mathlib's `SimpleGraph`, not an abstract predicate
whose fields include the desired conclusions. None requires finiteness.
-/

namespace MISLocal

variable {V : Type*} (G : SimpleGraph V)

/-- Delete each candidate having a candidate neighbor. -/
def repair (S : Set V) : Set V :=
  {v | v ∈ S ∧ ∀ w, G.Adj v w → w ∉ S}

theorem repair_subset (S : Set V) : repair G S ⊆ S :=
  fun _ h => h.1

theorem repair_independent (S : Set V) : G.IsIndepSet (repair G S) := by
  intro v hv w hw _ hAdj
  exact hv.2 w hAdj hw.1

theorem repair_of_independent {S : Set V} (hS : G.IsIndepSet S) :
    repair G S = S := by
  apply Set.Subset.antisymm (repair_subset G S)
  intro v hv
  exact ⟨hv, fun w hvw hw => hS hv hw hvw.ne hvw⟩

/-- Repair at a vertex depends only on candidates in its closed neighborhood. -/
theorem repair_local {S S' : Set V} {v : V}
    (hv : v ∈ S ↔ v ∈ S')
    (hn : ∀ w, G.Adj v w → (w ∈ S ↔ w ∈ S')) :
    v ∈ repair G S ↔ v ∈ repair G S' := by
  constructor
  · rintro ⟨hs, hns⟩
    exact ⟨hv.mp hs, fun w hw hsw => hns w hw ((hn w hw).mpr hsw)⟩
  · rintro ⟨hs, hns⟩
    exact ⟨hv.mpr hs, fun w hw hsw => hns w hw ((hn w hw).mp hsw)⟩

def Occupies (C S : Set V) : Prop := ∃ v, v ∈ C ∧ v ∈ S

theorem occupies_repair_of_independent {C S : Set V} (hS : G.IsIndepSet S) :
    Occupies C (repair G S) ↔ Occupies C S := by
  rw [repair_of_independent G hS]

theorem clique_independent_at_most_one {C S : Set V}
    (hC : G.IsClique C) (hS : G.IsIndepSet S)
    {v w : V} (hvC : v ∈ C) (hvS : v ∈ S)
    (hwC : w ∈ C) (hwS : w ∈ S) : v = w := by
  by_contra hne
  exact hS hvS hwS hne (hC hvC hwC hne)

/-- Inclusion-maximal, not maximum-cardinality, independent sets dominate. -/
theorem maximal_independent_dominates {S : Set V}
    (hS : Maximal G.IsIndepSet S) {v : V} (hv : v ∉ S) :
    ∃ w, w ∈ S ∧ G.Adj v w := by
  classical
  by_contra h
  have hn : ∀ w ∈ S, ¬G.Adj v w := by
    simpa only [not_exists, not_and] using h
  have hi : G.IsIndepSet (insert v S) := by
    intro x hx y hy hxy hAdj
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact G.irrefl hAdj
      · exact hn y hy hAdj
    · rcases hy with rfl | hy
      · exact hn x hx hAdj.symm
      · exact hS.1 hx hy hxy hAdj
  have hsub : insert v S ⊆ S := hS.2 hi (Set.subset_insert v S)
  exact hv (hsub (Set.mem_insert v S))

/-- The obstruction event. The witness is an actual independent set outside C. -/
def ExternallyDominatable (C : Set V) : Prop :=
  ∃ S : Set V, G.IsIndepSet S ∧ Disjoint C S ∧
    ∀ v ∈ C, ∃ w ∈ S, G.Adj v w

theorem maximal_occupies_of_not_externally_dominatable {C S : Set V}
    (hNo : ¬ExternallyDominatable G C)
    (hS : Maximal G.IsIndepSet S) : Occupies C S := by
  classical
  by_contra h
  have hd : Disjoint C S := Set.disjoint_left.mpr (by
    intro v hvC hvS
    exact h ⟨v, hvC, hvS⟩)
  apply hNo
  refine ⟨S, hS.1, hd, ?_⟩
  intro v hvC
  exact maximal_independent_dominates G hS
    (fun hvS => h ⟨v, hvC, hvS⟩)

/-- Local simulation agreement, plus actual independence, preserves occupancy. -/
theorem repair_occupancy_agrees {C S candidates : Set V}
    (hS : G.IsIndepSet S)
    (hlocal : ∀ v ∈ C, ∀ w, w = v ∨ G.Adj v w →
      (w ∈ candidates ↔ w ∈ S)) :
    Occupies C (repair G candidates) ↔ Occupies C S := by
  have heq : ∀ v ∈ C, v ∈ repair G candidates ↔ v ∈ S := by
    intro v hv
    rw [← repair_of_independent G hS]
    exact repair_local G (hlocal v hv v (Or.inl rfl))
      (fun w hw => hlocal v hv w (Or.inr hw))
  constructor
  · rintro ⟨v, hv, hs⟩
    exact ⟨v, hv, (heq v hv).mp hs⟩
  · rintro ⟨v, hv, hs⟩
    exact ⟨v, hv, (heq v hv).mpr hs⟩

end MISLocal
