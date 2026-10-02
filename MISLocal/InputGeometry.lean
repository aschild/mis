import MISLocal.LocalHomogeneity
import MISLocal.AnySourceEntropy
import MISLocal.GeometricCharging

/-! Coordinate geometry used by the occupancy theorem. All fields concern
finite incidence, coordinate containment, disjointness, or an explicit routing
certificate. No field assumes an entropy or probability estimate. Layers are
numbered in descending-radius order, avoiding natural-number subtraction. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def restrictObservation {I : Type*} [DecidableEq I] {T : I → Type*}
    (S : Finset I) (y : ∀ i, Option (T i)) : ∀ i, Option (T i) :=
  fun i => if i ∈ S then y i else none

theorem restrictObservation_observe {I : Type*} [DecidableEq I] {T : I → Type*}
    (S R : Finset I) (h : S ⊆ R) (x : ∀ i, T i) :
    restrictObservation S (observeInputs R x) = observeInputs S x := by
  funext i
  by_cases hi : i ∈ S
  · simp [restrictObservation, observeInputs, hi, h hi]
  · simp [restrictObservation, observeInputs, hi]

theorem observeInputs_readsOnly {I : Type*} [DecidableEq I] {T : I → Type*}
    (S R : Finset I) (h : S ⊆ R) : ReadsOnly (observeInputs (T := T) S) R := by
  intro x z hxz
  exact (observeInputs_eq_iff S x z).mpr (fun i hi => hxz i (h hi))

structure ProductInputGeometry (I V E : Type*) [DecidableEq I] [Fintype V] [Fintype E]
    (d r : ℕ) where
  left : E → V
  right : E → V
  noLoop : ∀ e, right e ≠ left e
  degree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1
  edgeCount : 2*Fintype.card E = (d+1)*Fintype.card V
  readers : V → Finset I
  vertex : ℕ → V → Finset I
  shared : ℕ → E → Finset I
  vertex_readers : ∀ j v, j ≤ r → vertex j v ⊆ readers v
  nested : ∀ j v, j < r → vertex (j+1) v ⊆ vertex j v
  empty_last : ∀ v, vertex r v = ∅
  contains : ∀ j v e, j ≤ r → edgeIncident left right v e → vertex j v ⊆ shared j e
  shared_inside : ∀ j v e, j < r → edgeIncident left right v e → shared (j+1) e ⊆ vertex j v
  endpoint_overlap : ∀ j e, j < r → vertex j (left e) ∩ vertex j (right e) ⊆ shared (j+1) e
  branch_overlap : ∀ j v e f, j ≤ r → e ≠ f → edgeIncident left right v e →
    edgeIncident left right v f → shared j e ∩ shared j f ⊆ vertex j v
  initial_reader_overlap : ∀ e, readers (left e) ∩ readers (right e) ⊆ shared 0 e
  initial_shared_overlap : ∀ v e, edgeIncident left right v e → readers v ∩ shared 0 e ⊆ vertex 0 v
  charge : ∀ j, j ≤ r → SourceCharge left right readers (vertex j) (shared j) d

namespace ProductInputGeometry

variable {I V E : Type*} [DecidableEq I] [Fintype V] [Fintype E] {d r : ℕ}
    (g : ProductInputGeometry I V E d r)

theorem endpoint_cover (v : V) : ∃ e b, endpoint g.left g.right e b = v := by
  have hc : 0 < (Finset.univ.filter (edgeIncident g.left g.right v)).card := by rw [g.degree]; omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp hc
  exact ((Finset.mem_filter.mp he).2).elim (fun h => ⟨e,false,h⟩) (fun h => ⟨e,true,h⟩)

def unconditionedCharge : SourceCharge g.left g.right g.readers (fun _ => ∅) (fun _ => ∅) d := by
  have c := g.charge r (le_refl r)
  have hv : g.vertex r = fun _ => ∅ := funext g.empty_last
  rw [hv] at c
  exact ⟨c.route,c.incident,fun _ _ => Finset.empty_subset _,fun _ _ => Finset.not_mem_empty _⟩

def vertexObservation {T : I → Type*} (j : ℕ) (v : V) : (∀ i, T i) → ∀ i, Option (T i) :=
  observeInputs (g.vertex j v)

def sharedObservation {T : I → Type*} (j : ℕ) (e : E) : (∀ i, T i) → ∀ i, Option (T i) :=
  observeInputs (g.shared j e)

theorem vertex_from_shared {T : I → Type*} (j : ℕ) (hj : j ≤ r) (v : V) (e : E)
    (hve : edgeIncident g.left g.right v e) (x : ∀ i, T i) :
    g.vertexObservation j v x = restrictObservation (g.vertex j v) (g.sharedObservation j e x) :=
  (restrictObservation_observe _ _ (g.contains j v e hj hve) x).symm

theorem next_shared_from_vertex {T : I → Type*} (j : ℕ) (hj : j < r) (v : V) (e : E)
    (hve : edgeIncident g.left g.right v e) (x : ∀ i, T i) :
    g.sharedObservation (j+1) e x = restrictObservation (g.shared (j+1) e) (g.vertexObservation j v x) :=
  (restrictObservation_observe _ _ (g.shared_inside j v e hj hve) x).symm

theorem endpoint_views_independent [Fintype I] {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (j : ℕ) (hj : j < r) (e : E) (y : ∀ i, Option (T i))
    (hy : 0 < ((FiniteProb.pi P).map (g.sharedObservation (j+1) e)).weight y) :
    ((FiniteProb.pi P).given (g.sharedObservation (j+1) e) y).Independent
      (fun b : Bool => if b then g.vertexObservation j (g.right e) else g.vertexObservation j (g.left e)) := by
  apply FiniteProb.conditional_independent_of_disjoint_reads P _
    (fun b : Bool => if b then g.vertex j (g.right e) else g.vertex j (g.left e)) (g.shared (j+1) e)
    (by intro b; cases b <;> exact observeInputs_readsOnly _ _ (Finset.Subset.refl _)) _ y hy
  intro b c hbc i hi hi'
  cases b <;> cases c
  · exact False.elim (hbc rfl)
  · exact g.endpoint_overlap j e hj (Finset.mem_inter.mpr ⟨hi,hi'⟩)
  · exact g.endpoint_overlap j e hj (Finset.mem_inter.mpr ⟨hi',hi⟩)
  · exact False.elim (hbc rfl)

theorem branch_views_independent [Fintype I] [DecidableEq E]
    {T : I → Type*} [∀ i, Fintype (T i)] (P : ∀ i, FiniteProb (T i))
    (j : ℕ) (hj : j ≤ r) (v : V) (y : ∀ i, Option (T i))
    (hy : 0 < ((FiniteProb.pi P).map (g.vertexObservation j v)).weight y) :
    ((FiniteProb.pi P).given (g.vertexObservation j v) y).Independent
      (fun e : {e // edgeIncident g.left g.right v e} => g.sharedObservation j e.val) := by
  apply FiniteProb.conditional_independent_of_disjoint_reads P _
    (fun e : {e // edgeIncident g.left g.right v e} => g.shared j e.val) (g.vertex j v)
    (fun e => observeInputs_readsOnly _ _ (Finset.Subset.refl _)) _ y hy
  intro e f hef i hi hi'
  exact g.branch_overlap j v e.val f.val hj (fun h => hef (Subtype.ext h)) e.property f.property
    (Finset.mem_inter.mpr ⟨hi,hi'⟩)

end ProductInputGeometry
end
end MISLocal
