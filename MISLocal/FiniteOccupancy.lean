import MISLocal.GeometricTruncation
import MISLocal.GeometricBudget
import MISLocal.OccupancyNumerics
import MISLocal.ListParameters

/-! Occupancy for a homogeneous finite independent-input geometry.

The algorithm is an actual local output function on a product probability
space. Short supports, projected conflicts, deleted masses and the scalar
overlap estimate are constructed/proved. The model hypotheses are coordinate
geometry and input/output symmetry; no target probability or entropy bound
is included in the model. `GraphOccupancy.lean` instantiates this geometry
with actual finite-graph round neighborhoods. No infinite-tree probability
space or infinite/finite transfer is asserted in this module.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem finite_occupancy_of_parameters {I V E A : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]
    {T : I → Type} [∀ i, Fintype (T i)] {d n : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d (n+1))
    (U : V → (∀ i, T i) → Option A)
    (hlocal : ∀ v, ReadsOnly (U v) (g.readers v))
    (hhom : ViewHomogeneous (pi P) U g.vertexObservation g.sharedObservation g.left g.right)
    (e₀ : E) (matrix : (∀ i, T i) → A × A → Bool)
    (decode : ℕ → (∀ i, Option (T i)) → A × A → Bool)
    (hdecode : ∀ j, j ≤ n+1 → ∀ ω, decode j (g.sharedObservation j e₀ ω) = matrix ω)
    (hmatrix : (pi P).map matrix = fairBits (A × A))
    (hzero : (pi P).prob (fun ω => selectedConflict (fun G a b => G (a,b)=true)
      (matrix ω,U (g.left e₀) ω,U (g.right e₀) ω)) = 0)
    (ell M m : ℕ) (hD : 12 ≤ (d:ℝ)+1) (hlog : 1 ≤ Real.log ((d:ℝ)+1))
    (hell : 0 < ell) (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*((d:ℝ)+1) ≤ ((d:ℝ)+1)^4)
    (hratio : (M:ℝ)/m = 1/((d:ℝ)+1)) (hmupper : (m:ℝ) ≤ ((d:ℝ)+1)^4)
    (hexception : (Fintype.card A:ℝ)^(2*ell)*Real.exp (-(ell:ℝ)^2/16) ≤ 1/((d:ℝ)+1)^2) :
    (pi P).prob (fun ω => U (g.left e₀) ω ≠ none) ≤ occupancyCap (n+1) ((d:ℝ)+1) := by
  let μ := pi P
  let W := g.vertexObservation (T := T)
  let F := g.sharedObservation (T := T)
  let Y := fun v j => W (j+1) v
  let S := fun j v => μ.survivor (U v) (Y v) m j
  let H := fun j v => μ.firstDeleted (U v) (Y v) m j
  let p := μ.prob (fun ω => U (g.left e₀) ω ≠ none)
  let pf := μ.prob (fun ω => S (n+1) (g.left e₀) ω ≠ none)
  let τ := fun j : Fin (n+1) => μ.prob (fun ω => H j.val (g.left e₀) ω ≠ none)
  let conflict := fun (j : ℕ) (Z : V → (∀ i, T i) → Option A) => μ.kernelConflict
    (fun ω => (μ.given (W j (g.left e₀)) (W j (g.left e₀) ω)).map (Z (g.left e₀)))
    (fun ω => (μ.given (W j (g.right e₀)) (W j (g.right e₀) ω)).map (Z (g.right e₀))) matrix
  let w := fun j => conflict j (H j)
  let ε := conflict (n+1) (S (n+1))
  have hDp : 0 < (d:ℝ)+1 := by positivity
  have hmreal : (0:ℝ) < m := by exact_mod_cast hm
  have hmone : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hSloc (j : ℕ) (hj : j ≤ n+1) (v : V) : ReadsOnly (S j v) (g.readers v) :=
    μ.survivor_readsOnly (U v) (Y v) m j (g.readers v) (hlocal v)
      (fun i hi => observeInputs_readsOnly _ _ (g.vertex_readers (i+1) v (by omega)))
  have hHloc (j : ℕ) (hj : j < n+1) (v : V) : ReadsOnly (H j v) (g.readers v) :=
    μ.firstDeleted_readsOnly (U v) (Y v) m j (g.readers v) (hlocal v)
      (fun i hi => observeInputs_readsOnly _ _ (g.vertex_readers (i+1) v (by omega)))
  have hShom (j : ℕ) : ViewHomogeneous μ (S j) W F g.left g.right := hhom.survivor m j
  have hHhom (j : ℕ) : ViewHomogeneous μ (H j) W F g.left g.right := hhom.firstDeleted m j
  have hHzero (j : ℕ) : μ.prob (fun ω => selectedConflict (fun G a b => G (a,b)=true)
      (matrix ω,H j (g.left e₀) ω,H j (g.right e₀) ω)) = 0 :=
    μ.zero_conflict_of_restrictions _ _ _ _ matrix _
      (μ.firstDeleted_some_original (U (g.left e₀)) (Y (g.left e₀)) m j)
      (μ.firstDeleted_some_original (U (g.right e₀)) (Y (g.right e₀)) m j) hzero
  have hbad : μ.prob (fun ω => exceptionalMatrix ell (matrix ω)) ≤ 1/((d:ℝ)+1)^2 := by
    rw [← μ.prob_map matrix (exceptionalMatrix ell), hmatrix]
    exact (exceptional_matrix_probability ell).trans hexception
  have hloss (j : Fin (n+1)) : τ j ≤ 2100*Real.log ((d:ℝ)+1)/((d:ℝ)+1)+6*Real.sqrt (w j.val) := by
    have hjs : j.val+1 ≤ n+1 := Nat.succ_le_of_lt j.isLt
    have h := geometric_truncation P g (H j.val) (hHhom j.val) j.val j.isLt e₀ ell M m
      hD hlog hell hM hm hellM hsize hratio
      (fun v b hb a => μ.deleted_given_atom_le (S j.val v) (W (j.val+1) v) hm b hb a)
      (decode (j.val+1)) (by simpa only [hdecode (j.val+1) hjs] using hbad) (le_refl _)
    simpa only [hdecode (j.val+1) hjs] using h
  have hw0 : w 0 = 0 := by
    have h := initial_projection_conflict P g (H 0) (hHloc 0 (by omega)) e₀ (decode 0)
    have hd := hdecode 0 (by omega)
    have hz : μ.prob (fun ω => selectedConflict (fun b a a' => decode 0 b (a,a')=true)
        (F 0 e₀ ω,H 0 (g.left e₀) ω,H 0 (g.right e₀) ω)) = 0 := by
      change μ.prob (fun ω => selectedConflict (fun G a b => G (a,b)=true)
        (decode 0 (F 0 e₀ ω),H 0 (g.left e₀) ω,H 0 (g.right e₀) ω)) = 0
      simpa only [F, hd] using hHzero 0
    have he : w 0 = μ.prob (fun ω => selectedConflict (fun b a a' => decode 0 b (a,a')=true)
        (F 0 e₀ ω,H 0 (g.left e₀) ω,H 0 (g.right e₀) ω)) := by
      simpa only [hd] using h
    exact he.trans hz
  have hfair (a b : A) : μ.prob (fun ω => matrix ω (a,b)=true) = 1/2 := by
    rw [← μ.prob_map matrix (fun G => G (a,b)=true), hmatrix]
    exact fairBits_coordinate (a,b)
  have hfinal : pf^2 = 2*ε := by
    have hg (v : V) (ω : ∀ i, T i) : μ.given (W (n+1) v) (W (n+1) v ω) = μ := by
      change μ.given (observeInputs (g.vertex (n+1) v)) _ = μ
      rw [g.empty_last, given_empty_observation]
    have hdist := (hShom (n+1)).output_distribution e₀ (g.right e₀) (g.endpoint_cover _)
    have he : ε = pf*pf*(1/2) := by
      dsimp [ε, conflict]
      simp only [hg]
      rw [hdist, kernelConflict_constant μ _ _ matrix hfair, prob_map]
    rw [he]
    ring
  let J : Option (Fin n) → ℕ := fun i => match i with | none => n+1 | some i => i.val+1
  let B := fun i v => μ.budgetPart (U v) (Y v) m n i
  let bmass := fun i => μ.prob (fun ω => B i (g.left e₀) ω ≠ none)
  let bw := fun i => conflict (J i) (B i)
  have hBlocal (i : Option (Fin n)) (v : V) : ReadsOnly (B i v) (g.readers v) := by
    cases i with
    | none => exact hSloc (n+1) (le_refl _) v
    | some i => exact hHloc (i.val+1) (by omega) v
  have hBhom (i : Option (Fin n)) : ViewHomogeneous μ (B i) W F g.left g.right := by
    cases i with
    | none => exact hShom (n+1)
    | some i => exact hHhom (i.val+1)
  have hbudget_each (i : Option (Fin n)) : bw i ≤ 2*massBudget (m:ℝ) (bmass i)/((d:ℝ)+1) := by
    let prev : ℕ := match i with | none => n | some i => i.val
    let L := fun b => ((μ.given (W (J i) (g.left e₀)) b).map (S prev (g.left e₀))).outputList m
    have hJ : J i ≤ n+1 := by cases i with | none => rfl | some i => dsimp [J]; omega
    have hsupport (b) (hb : 0 < (μ.map (W (J i) (g.left e₀))).weight b) (a : A) (ha : a ∉ L b) :
        ((μ.given (W (J i) (g.left e₀)) b).map (B i (g.left e₀))).weight (some a) = 0 := by
      cases i with
      | none => exact μ.survivor_short_support (U (g.left e₀)) (Y (g.left e₀)) m n b hb a ha
      | some i => exact μ.firstDeleted_short_support (U (g.left e₀)) (Y (g.left e₀)) m i.val b hb a ha
    have hz := μ.budgetPart_zero_conflict (U (g.left e₀)) (U (g.right e₀))
      (Y (g.left e₀)) (Y (g.right e₀)) m n matrix (fun G a b => G (a,b)=true) hzero i
    have hz' : μ.prob (fun ω => selectedConflict (fun b a a' => decode (J i) b (a,a')=true)
        (F (J i) e₀ ω,B i (g.left e₀) ω,B i (g.right e₀) ω)) = 0 := by
      change μ.prob (fun ω => selectedConflict (fun G a b => G (a,b)=true)
        (decode (J i) (F (J i) e₀ ω),B i (g.left e₀) ω,B i (g.right e₀) ω)) = 0
      simpa only [F, hdecode (J i) hJ] using hz
    have h := geometric_projection_budget P g (B i) (hBlocal i) (hBhom i) (J i) hJ e₀ L hmreal
      (fun b => by exact_mod_cast bestList_card _ m) hsupport (decode (J i)) hz'
    simpa only [hdecode _ hJ] using h
  have hbtotal := joint_conflict_budget bmass bw hDp hmone (fun i => μ.prob_nonneg _)
    (μ.prob_le_one (fun ω => U (g.left e₀) ω ≠ none))
    (μ.budgetPart_mass_le (U (g.left e₀)) (Y (g.left e₀)) m n) hbudget_each
  have hbudget : ε + (∑ j : Fin (n+1), w j.val) ≤
      2*massBudget ((m:ℝ)*(n+1:ℕ)) p/((d:ℝ)+1) := by
    have he : (∑ j : Fin (n+1), w j.val) = ∑ i : Fin n, w (i.val+1) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, hw0, zero_add, Fin.val_succ]
    rw [he]
    simpa only [Fintype.sum_option, Fintype.card_option, Fintype.card_fin, bw, B, J, budgetPart,
      S, H, ε, w, p, bmass] using hbtotal
  have hmass : p = pf + ∑ j, τ j := by
    have h := μ.ancestor_mass_partition (U (g.left e₀)) (Y (g.left e₀)) m (n+1)
    simpa only [τ, H, ← Fin.sum_univ_eq_sum_range
      (fun j => μ.prob (fun ω => μ.firstDeleted (U (g.left e₀)) (Y (g.left e₀)) m j ω ≠ none)) (n+1)] using h.symm
  exact occupancy_from_reduction_estimates τ (fun j => w j.val) (by omega) hDp hlog hmreal hmupper
    (μ.prob_nonneg _) (μ.prob_le_one _) (fun j => μ.kernelConflict_nonneg _ _ _)
    (μ.kernelConflict_nonneg _ _ _) (μ.prob_nonneg _) hfinal hmass hloss hbudget

/-- The uniform parameter theorem. All list capacities and the exceptional
matrix estimate are instantiated explicitly. `GraphOccupancy.lean` supplies
the concrete graph-neighborhood specialization. -/
theorem finite_occupancy {I V E : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype E] [DecidableEq E] {T : I → Type} [∀ i, Fintype (T i)] {d n k : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d (n+1))
    (U : V → (∀ i, T i) → Option (Fin k))
    (hlocal : ∀ v, ReadsOnly (U v) (g.readers v))
    (hhom : ViewHomogeneous (pi P) U g.vertexObservation g.sharedObservation g.left g.right)
    (e₀ : E) (matrix : (∀ i, T i) → Fin k × Fin k → Bool)
    (decode : ℕ → (∀ i, Option (T i)) → Fin k × Fin k → Bool)
    (hdecode : ∀ j, j ≤ n+1 → ∀ ω, decode j (g.sharedObservation j e₀ ω) = matrix ω)
    (hmatrix : (pi P).map matrix = fairBits (Fin k × Fin k))
    (hzero : (pi P).prob (fun ω => selectedConflict (fun G a b => G (a,b)=true)
      (matrix ω,U (g.left e₀) ω,U (g.right e₀) ω)) = 0)
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (pi P).prob (fun ω => U (g.left e₀) ω ≠ none) ≤ occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  obtain ⟨hell,hM,hm,hellM,hcap,hratio,hlog⟩ := explicit_list_parameters hD hk hlower hupper
  have hD12 : (12:ℝ) ≤ ((d+1:ℕ):ℝ) := by exact_mod_cast (show 12 ≤ d+1 by omega)
  have hsize : (listMiddle k:ℝ)*((d+1:ℕ):ℝ) ≤ ((d+1:ℕ):ℝ)^4 := by
    simpa only [listCapacity, Nat.cast_mul, mul_comm] using hcap
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have helllower := (listEll_bounds hk (show (1:ℝ) ≤ ((d+1:ℕ):ℝ) by linarith) hlower hupper).1
  have hx := matrix_numeric_bound hD12 hkpos hlower helllower
  have h := finite_occupancy_of_parameters P g U hlocal hhom e₀ matrix decode hdecode hmatrix hzero
    (listEll k) (listMiddle k) (listCapacity (d+1) k)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hD12)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hlog)
    hell hM hm hellM
    (by simpa only [Nat.cast_add, Nat.cast_one] using hsize)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hratio)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hcap)
    (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hx)
  simpa only [Nat.cast_add, Nat.cast_one] using h

end FiniteProb
end
end MISLocal
