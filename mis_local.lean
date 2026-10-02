import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finset.Max
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option warningAsError true

/-!
ANONYMOUS OCCUPANCY AND ASYMPTOTIC RANDOMIZED LOCAL MIS LOWER BOUND PROVED.

MISLocal.randomized_LOCAL_MIS_iid_not_littleO proves that a measurable
uniform LOCAL program family, correct with probability at least 2/3 on
every n-vertex graph, cannot have o(log n / log log n) worst-case rounds.
The state and tape spaces and program may depend on n. Infinite private
tapes are allowed. The only algorithmic premises are measurability and
MIS correctness. No reduction, skeleton-existence, symmetry, probability
estimate or asymptotic numerical inequality is assumed.

MISLocal.TreeGeometry.anonymous_graph_occupancy proves
p <= min(1,5000*r*log D/D) for anonymous radius-r rules on finite D-regular
graphs with the displayed tree neighborhoods, independent fair edge matrices
and iid finite private vertex values. D >= 1048576 and D <= log k <= D^2
are explicit. An AnonymousRule is one function on rooted matrix-labeled views
modulo vertex/edge renaming and edge-orientation reversal. Skeleton names
cannot be inspected. Locality and ViewHomogeneous are proved from this
definition and constructed regular-tree-neighborhood isomorphisms.
The entropy, truncation, ancestor, projection-budget and final-conflict estimates
are proved, not assumed. InputRelabeling derives probability preservation
from coordinate weights. The original graph_occupancy remains a more general
internal theorem with an explicit symmetry premise. AnonymousTapeReduction
applies the anonymous bound inside the fixed-tape averaging and
finite obstruction. ConcreteFiniteObstruction now constructs the actual
clique blow-up, jointly uniform matrix-derived IDs, collision gate, anonymous
quotient rule, global repaired process, zero conflict, local legal-ID
completion, collision and external-domination estimates. LocalGraphRealization
preserves a local execution on a legal n-vertex input with isolated padding.
FiniteRegularSkeleton constructs actual finite regular graphs with arbitrary
tree neighborhood depth from involutions on bounded reduced words.
PowerSizeParameters and PowerBallEstimates discharge all finite inequalities.
AsymptoticLocalLowerBound concludes using the powers-of-two size subsequence.
The iid corollary uses the actual product measure of arbitrary private tapes.
See README.md in the accompanying project archive for the exact scope.

This file mechanically concatenates the project's modules, audit, and tests.
Do not import MISLocal as well: the declarations would then be duplicated.
-/

/- ===== Source: MISLocal/FiniteProbability.lean ===== -/

/-!
# Finite probability with explicit nonnegative normalized weights

All probability arithmetic is in `ℝ`. An empty sample space cannot carry a
`FiniteProb`: the normalization field rules it out. No division by its cardinality
is used unless a `Nonempty` instance is supplied.
-/

open scoped BigOperators
open scoped Classical

namespace MISLocal

noncomputable section

def bit (p : Prop) : ℝ := if p then 1 else 0

@[simp] theorem bit_true : bit True = 1 := by simp [bit]
@[simp] theorem bit_false : bit False = 0 := by simp [bit]

theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by
  classical
  by_cases h : p <;> simp [bit, h]

theorem bit_le_one (p : Prop) : bit p ≤ 1 := by
  classical
  by_cases h : p <;> simp [bit, h]

theorem bit_mono {p q : Prop} (h : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [bit, hp, h hp]
  · simp only [bit, if_neg hp]
    exact bit_nonneg q

theorem bit_not (p : Prop) : bit (¬p) = 1 - bit p := by
  classical
  by_cases h : p <;> simp [bit, h]

theorem bit_or_le (p q : Prop) : bit (p ∨ q) ≤ bit p + bit q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem bit_and_lower (p q : Prop) : bit p + bit q - 1 ≤ bit (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

structure FiniteProb (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteProb

variable {Ω : Type*} [Fintype Ω] (μ : FiniteProb Ω)

def expect (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

def prob (p : Ω → Prop) : ℝ := μ.expect (fun ω => bit (p ω))

theorem expect_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    μ.expect f = μ.expect g := by
  simp only [expect, h]

@[simp] theorem expect_const (a : ℝ) : μ.expect (fun _ => a) = a := by
  simp [expect, ← Finset.sum_mul, μ.total]

theorem expect_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem expect_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (h ω))

theorem expect_add (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (a : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => a * f ω) = a * μ.expect f := by
  simp [expect, ← Finset.mul_sum, mul_left_comm]

theorem expect_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_le_const {f : Ω → ℝ} {b : ℝ} (h : ∀ ω, f ω ≤ b) :
    μ.expect f ≤ b := by
  simpa using μ.expect_mono h

theorem const_le_expect {f : Ω → ℝ} {b : ℝ} (h : ∀ ω, b ≤ f ω) :
    b ≤ μ.expect f := by
  simpa using μ.expect_mono h

theorem prob_congr {p q : Ω → Prop} (h : ∀ ω, p ω ↔ q ω) :
    μ.prob p = μ.prob q := by
  unfold prob
  exact μ.expect_congr (fun ω => congrArg bit (propext (h ω)))

theorem prob_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) :
    μ.prob p ≤ μ.prob q := μ.expect_mono (fun ω => bit_mono (h ω))

theorem prob_nonneg (p : Ω → Prop) : 0 ≤ μ.prob p :=
  μ.expect_nonneg (fun ω => bit_nonneg (p ω))

theorem prob_le_one (p : Ω → Prop) : μ.prob p ≤ 1 :=
  μ.expect_le_const (fun ω => bit_le_one (p ω))

@[simp] theorem prob_true : μ.prob (fun _ => True) = 1 := by simp [prob]
@[simp] theorem prob_false : μ.prob (fun _ => False) = 0 := by simp [prob]

theorem prob_not (p : Ω → Prop) : μ.prob (fun ω => ¬p ω) = 1 - μ.prob p := by
  simp only [prob, bit_not, expect_sub, expect_const]

theorem prob_or_le (p q : Ω → Prop) :
    μ.prob (fun ω => p ω ∨ q ω) ≤ μ.prob p + μ.prob q := by
  simpa only [prob, expect_add] using μ.expect_mono (fun ω => bit_or_le (p ω) (q ω))

theorem prob_and_lower (p q : Ω → Prop) :
    μ.prob p + μ.prob q - 1 ≤ μ.prob (fun ω => p ω ∧ q ω) := by
  simpa only [prob, expect_sub, expect_add, expect_const] using
    μ.expect_mono (fun ω => bit_and_lower (p ω) (q ω))

theorem prob_exists_le_sum {ι : Type*} [Fintype ι] (p : ι → Ω → Prop) :
    μ.prob (fun ω => ∃ i, p i ω) ≤ ∑ i, μ.prob (p i) := by
  classical
  unfold prob
  rw [← μ.expect_sum Finset.univ (fun i ω => bit (p i ω))]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i, p i ω
  · obtain ⟨i, hi⟩ := h
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => bit (p j ω)) (fun j _ => bit_nonneg (p j ω)) (Finset.mem_univ i)
    simpa only [bit, if_pos hi, if_pos (show ∃ i, p i ω from ⟨i, hi⟩)] using hs
  · simp only [bit, if_neg h]
    exact Finset.sum_nonneg (fun i _ => bit_nonneg (p i ω))

/-- Uniform probability is defined only on a nonempty finite type. -/
def uniform (α : Type*) [Fintype α] [Nonempty α] : FiniteProb α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [h]

theorem uniform_prob_eq_card {α : Type*} [Fintype α] [Nonempty α]
    (p : α → Prop) :
    (uniform α).prob p = (Fintype.card {a // p a} : ℝ) / Fintype.card α := by
  classical
  change (∑ x, (Fintype.card α : ℝ)⁻¹ * bit (p x)) = _
  rw [← Finset.mul_sum]
  simp [bit, Fintype.card_subtype, div_eq_mul_inv, mul_comm]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/Repair.lean ===== -/

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


/- ===== Source: MISLocal/Identifiers.lean ===== -/

/-!
# Legal ID completion and tape reindexing

Identifiers use `Fin n`, i.e. 0 through n-1. This is equivalent to paper IDs
1 through n. Completion is a genuine permutation; it does not merely assert
that each locally visible identifier is legal.
-/

open scoped BigOperators
open scoped Classical

namespace MISLocal
noncomputable section

theorem exists_id_completion {n : ℕ} (U : Set (Fin n)) (f : Fin n → Fin n)
    (hinj : Set.InjOn f U) :
    ∃ e : Equiv.Perm (Fin n), ∀ v ∈ U, e v = f v := by
  classical
  let i : U ↪ Fin n := ⟨fun x => f x, fun x y h =>
    Subtype.ext (hinj x.property y.property h)⟩
  let e : U ≃ Set.range i := Equiv.ofInjective i i.injective
  refine ⟨e.extendSubtype, ?_⟩
  intro v hv
  simpa [e, i] using e.extendSubtype_apply_of_mem v hv

/-- The external completion depends only on the tentative ID map and U. -/
def completeIDs {n : ℕ} (U : Set (Fin n)) (f : Fin n → Fin n) :
    Equiv.Perm (Fin n) :=
  if h : Set.InjOn f U then (exists_id_completion U f h).choose else Equiv.refl _

theorem completeIDs_agrees {n : ℕ} (U : Set (Fin n)) (f : Fin n → Fin n)
    (hinj : Set.InjOn f U) (v : Fin n) (hv : v ∈ U) :
    completeIDs U f v = f v := by
  classical
  simp only [completeIDs, dif_pos hinj]
  exact (exists_id_completion U f hinj).choose_spec v hv

theorem completeIDs_bijective {n : ℕ} (U : Set (Fin n)) (f : Fin n → Fin n) :
    Function.Bijective (completeIDs U f) := (completeIDs U f).bijective

/-- Pull an ID-indexed tape table back to vertices. No finiteness of Tape is needed. -/
def reindexTapes {V ID Tape : Type*} (ids : V ≃ ID) : (ID → Tape) ≃ (V → Tape) where
  toFun W v := W (ids v)
  invFun W i := W (ids.symm i)
  left_inv W := by funext i; simp
  right_inv W := by funext v; simp

/-- A permutation of coordinates preserves the exact finite-product weight. -/
theorem tape_product_weight {V ID Tape : Type*} [Fintype V] [Fintype ID]
    (ids : V ≃ ID) (weight : Tape → ℝ) (W : ID → Tape) :
    (∏ v, weight (reindexTapes ids W v)) = ∏ i, weight (W i) := by
  exact ids.prod_comp (fun i => weight (W i))

/-- This is distributional equality for arbitrary finite tape distributions,
not just fair tapes. Since it holds for each bijection, the bijection may depend
on a separately fixed graph. The tape table may not influence that choice. -/
theorem tape_weighted_sum_reindex {V ID Tape : Type*}
    [Fintype V] [Fintype ID] [Fintype Tape]
    (ids : V ≃ ID) (weight : Tape → ℝ) (test : (V → Tape) → ℝ) :
    (∑ W : ID → Tape, (∏ i, weight (W i)) * test (reindexTapes ids W)) =
      ∑ W : V → Tape, (∏ v, weight (W v)) * test W := by
  convert (reindexTapes (Tape := Tape) ids).sum_comp
    (fun W => (∏ v, weight (W v)) * test W) using 1
  apply Finset.sum_congr rfl
  intro W _
  rw [tape_product_weight]

/-- Reduction modulo n has at most two preimages when m ≤ 2n. -/
theorem modulo_fiber_card_le_two {n m : ℕ} (hn : 0 < n) (hm : m ≤ 2 * n)
    (a : Fin n) :
    Fintype.card {x : Fin m // x.val % n = a.val} ≤ 2 := by
  let q : {x : Fin m // x.val % n = a.val} → Fin 2 :=
    fun x => ⟨x.val.val / n, (Nat.div_lt_iff_lt_mul hn).mpr
      (lt_of_lt_of_le x.val.isLt (by simpa [Nat.mul_comm] using hm))⟩
  have hq : Function.Injective q := by
    intro x y h
    have heq : x.val.val / n = y.val.val / n := congrArg Fin.val h
    have hx := Nat.mod_add_div x.val.val n
    have hy := Nat.mod_add_div y.val.val n
    rw [x.property] at hx
    rw [y.property, ← heq] at hy
    apply Subtype.ext
    apply Fin.ext
    omega
  simpa using Fintype.card_le_of_injective q hq

theorem modulo_point_probability {n m : ℕ} (hn : 0 < n)
    (hnm : n ≤ m) (hm : m ≤ 2 * n) (a : Fin n) :
    letI : NeZero m := ⟨by omega⟩
    (FiniteProb.uniform (Fin m)).prob (fun x => x.val % n = a.val) ≤ 2 / (n : ℝ) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  rw [FiniteProb.uniform_prob_eq_card, Fintype.card_fin]
  have hc : (Fintype.card {x : Fin m // x.val % n = a.val} : ℝ) ≤ 2 := by
    exact_mod_cast modulo_fiber_card_le_two hn hm a
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le hn hnm
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hratio := (div_le_div_of_nonneg_right hc hm'.le).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hn' hnm')
  simpa using hratio

end
end MISLocal


/- ===== Source: MISLocal/Extraction.lean ===== -/

/-!
# The algebra behind directed-block XOR extraction

The source is an array of independent uniform outgoing strings, with one
coordinate per vertex and incident edge. Summing over incident edges gives a
jointly uniform array of vertex strings. Specialize the finite additive group
to `Fin q → ZMod 2` for q-bit strings and bitwise XOR.

The proof chooses a distinguished incident edge only to count fibers. The
extractor itself is the sum over ALL incident edges and is permutation invariant.
This module does not construct skeleton edge-matrix coordinates or prove their
identification with this product sample space.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

/-- The opposite off-diagonal blocks of an edge matrix are disjoint. -/
theorem directed_blocks_disjoint {K : Type*} (P : Set K) :
    Disjoint (P ×ˢ Pᶜ) (Pᶜ ×ˢ P) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hy.1 hx.1

def sumSplit {I A : Type*} [Fintype I] [AddCommGroup A] (j : I) :
    (I → A) ≃ A × ({i : I // i ≠ j} → A) :=
  (Equiv.funSplitAt j A).trans
    { toFun := fun x => (x.1 + ∑ i, x.2 i, x.2)
      invFun := fun x => (x.1 - ∑ i, x.2 i, x.2)
      left_inv := by intro x; ext <;> simp
      right_inv := by intro x; ext <;> simp }

theorem sumSplit_first {I A : Type*} [Fintype I] [AddCommGroup A]
    (j : I) (x : I → A) : (sumSplit j x).1 = ∑ i, x i := by
  exact (Fintype.sum_eq_add_sum_subtype_ne x j).symm

/-- A bijection between all source arrays and (all vertex sums, unused freedom). -/
def jointSumSplit {V I A : Type*} [Fintype I] [AddCommGroup A] (j : I) :
    (V → I → A) ≃ (V → A) × (V → {i : I // i ≠ j} → A) where
  toFun x := (fun v => (sumSplit j (x v)).1, fun v => (sumSplit j (x v)).2)
  invFun x v := (sumSplit j).symm (x.1 v, x.2 v)
  left_inv x := by
    funext v
    exact (sumSplit j).symm_apply_apply (x v)
  right_inv x := by
    apply Prod.ext <;> funext v
    · exact congrArg Prod.fst ((sumSplit j).apply_symm_apply (x.1 v, x.2 v))
    · exact congrArg Prod.snd ((sumSplit j).apply_symm_apply (x.1 v, x.2 v))

theorem jointSumSplit_first {V I A : Type*} [Fintype I] [AddCommGroup A]
    (j : I) (x : V → I → A) : (jointSumSplit j x).1 = fun v => ∑ i, x v i := by
  funext v
  exact sumSplit_first j (x v)

/-- Exact fiber counting for a coordinate of a finite product. -/
theorem uniform_first_coordinate {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Nonempty Ω] [Nonempty B]
    (e : Ω ≃ A × B) (a : A) :
    (FiniteProb.uniform Ω).prob (fun x => (e x).1 = a) =
      1 / (Fintype.card A : ℝ) := by
  let ef : {x : Ω // (e x).1 = a} ≃ B :=
    { toFun := fun x => (e x).2
      invFun := fun b => ⟨e.symm (a, b), by simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply e.injective
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext x.property.symm rfl
      right_inv := by intro b; simp }
  rw [FiniteProb.uniform_prob_eq_card]
  have hf : Fintype.card {x : Ω // (e x).1 = a} = Fintype.card B := Fintype.card_congr ef
  have hΩ : Fintype.card Ω = Fintype.card A * Fintype.card B := by
    simpa using Fintype.card_congr e
  rw [hf, hΩ, Nat.cast_mul]
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [one_mul] using (mul_div_mul_right (1 : ℝ) (Fintype.card A : ℝ) hB)

/-- The whole vector of sums is uniform, not merely each individual sum. -/
theorem outgoing_sums_jointly_uniform {V I A : Type*}
    [Fintype V] [Fintype I] [Fintype A] [AddCommGroup A]
    (j : I) (target : V → A) :
    (FiniteProb.uniform (V → I → A)).prob
      (fun x => (fun v => ∑ i, x v i) = target) =
        1 / (Fintype.card (V → A) : ℝ) := by
  have h := uniform_first_coordinate (jointSumSplit (V := V) (A := A) j) target
  simpa only [jointSumSplit_first] using h

/-- Symmetry of the extractor; the proof's distinguished edge is not an input. -/
theorem outgoing_sum_branch_invariant {I A : Type*} [Fintype I] [AddCommGroup A]
    (e : Equiv.Perm I) (x : I → A) : (∑ i, x (e i)) = ∑ i, x i :=
  Equiv.sum_comp e x

end
end MISLocal


/- ===== Source: MISLocal/Collisions.lean ===== -/

/-!
# Collision probabilities, including the factor of two

The ordered-pair proof counts both (i,j) and (j,i) whenever a collision occurs.
The resulting bound is L(L-1)/n, not 2L(L-1)/n. The natural subtraction in the
off-diagonal cardinality is cast only after proving the requisite inequality.
The statement itself uses real subtraction and also covers L = 0 and L = 1.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

variable {Ω : Type*} [Fintype Ω] (μ : FiniteProb Ω)

theorem collision_probability_le {ID : Type*} [Fintype ID]
    (X Y : Ω → ID) (c : ℝ)
    (hind : ∀ a b, μ.prob (fun ω => X ω = a ∧ Y ω = b) =
      μ.prob (fun ω => X ω = a) * μ.prob (fun ω => Y ω = b))
    (hpoint : ∀ a, μ.prob (fun ω => X ω = a) ≤ c) :
    μ.prob (fun ω => X ω = Y ω) ≤ c := by
  have heq : μ.prob (fun ω => X ω = Y ω) =
      ∑ a, μ.prob (fun ω => X ω = a ∧ Y ω = a) := by
    unfold FiniteProb.prob
    rw [← μ.expect_sum]
    apply μ.expect_congr
    intro ω
    by_cases h : X ω = Y ω
    · simp [bit, h]
    · have hh (a : ID) : ¬(X ω = a ∧ Y ω = a) := by
        rintro ⟨hx, hy⟩
        exact h (hx.trans hy.symm)
      simp [bit, h, hh]
  have hsum : (∑ a, μ.prob (fun ω => Y ω = a)) = 1 := by
    unfold FiniteProb.prob
    rw [← μ.expect_sum]
    simp [bit]
  rw [heq]
  calc
    _ = ∑ a, μ.prob (fun ω => X ω = a) * μ.prob (fun ω => Y ω = a) := by
      simp only [hind]
    _ ≤ ∑ a, c * μ.prob (fun ω => Y ω = a) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (hpoint a) (μ.prob_nonneg _)
    _ = c := by rw [← Finset.mul_sum, hsum, mul_one]

/-- A union bound requiring only pairwise collision bounds, not full independence. -/
theorem local_collision_bound {I ID : Type*} [Fintype I]
    (X : I → Ω → ID) (n : ℕ) (hn : 0 < n)
    (hpair : ∀ i j, i ≠ j → μ.prob (fun ω => X i ω = X j ω) ≤ 2 / (n : ℝ)) :
    μ.prob (fun ω => ¬Function.Injective (fun i => X i ω)) ≤
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) / (n : ℝ) := by
  let pairs : Finset (I × I) := Finset.univ.offDiag
  have hpoint (ω : Ω) :
      2 * bit (¬Function.Injective (fun i => X i ω)) ≤
        ∑ p ∈ pairs, bit (X p.1 ω = X p.2 ω) := by
    by_cases hinj : Function.Injective (fun i => X i ω)
    · simp only [bit, not_true_eq_false, hinj, if_false, mul_zero]
      exact Finset.sum_nonneg (fun p _ => bit_nonneg _)
    · obtain ⟨i, j, heq, hne⟩ : ∃ i j, X i ω = X j ω ∧ i ≠ j := by
        unfold Function.Injective at hinj
        push_neg at hinj
        exact hinj
      have hp : (i, j) ≠ (j, i) := by
        intro h
        exact hne (congrArg Prod.fst h)
      have hsub : ({(i, j), (j, i)} : Finset (I × I)) ⊆ pairs := by
        intro p hp'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
        rcases hp' with rfl | rfl <;> simp [pairs, hne, hne.symm]
      have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ => bit_nonneg (X p.1 ω = X p.2 ω))
      have hsmall : (∑ p ∈ ({(i, j), (j, i)} : Finset (I × I)),
          bit (X p.1 ω = X p.2 ω)) = 2 := by
        rw [Finset.sum_pair hp]
        simp only [Prod.fst, Prod.snd, bit, if_pos heq, if_pos heq.symm]
        norm_num
      rw [hsmall] at hs
      simpa only [bit, if_pos hinj, mul_one] using hs
  have hmean := μ.expect_mono hpoint
  rw [μ.expect_mul, μ.expect_sum] at hmean
  have hsum : (∑ p ∈ pairs, μ.prob (fun ω => X p.1 ω = X p.2 ω)) ≤
      (pairs.card : ℝ) * (2 / (n : ℝ)) := by
    calc
      _ ≤ ∑ _p ∈ pairs, 2 / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpair p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
      _ = _ := by simp
  have hcast : (pairs.card : ℝ) =
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) := by
    have hle : Fintype.card I ≤ Fintype.card I * Fintype.card I := Nat.le_mul_self _
    simp only [pairs, Finset.offDiag_card, Finset.card_univ, Nat.cast_sub hle,
      Nat.cast_mul]
    ring
  rw [hcast] at hsum
  change 2 * μ.prob (fun ω => ¬Function.Injective (fun i => X i ω)) ≤ _ at hmean
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := hmean.trans hsum
  rw [← mul_div_assoc] at h
  have hh := (le_div_iff₀ hn').mp h
  apply (le_div_iff₀ hn').mpr
  nlinarith

/-- Apply the pairwise-independent ID hypothesis and the maximum point mass. -/
theorem local_collision_bound_of_pairwise_independent {I ID : Type*}
    [Fintype I] [Fintype ID] (X : I → Ω → ID) (n : ℕ) (hn : 0 < n)
    (hind : ∀ i j, i ≠ j → ∀ a b,
      μ.prob (fun ω => X i ω = a ∧ X j ω = b) =
        μ.prob (fun ω => X i ω = a) * μ.prob (fun ω => X j ω = b))
    (hpoint : ∀ i a, μ.prob (fun ω => X i ω = a) ≤ 2 / (n : ℝ)) :
    μ.prob (fun ω => ¬Function.Injective (fun i => X i ω)) ≤
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) / (n : ℝ) := by
  apply local_collision_bound μ X n hn
  intro i j hij
  exact collision_probability_le μ (X i) (X j) (2 / (n : ℝ))
    (hind i j hij) (hpoint i)

end
end MISLocal


/- ===== Source: MISLocal/TapeAveraging.lean ===== -/

/-!
# Fixing a possibly infinite tape table, then averaging

The graph sample type is finite. The tape-table space is an arbitrary measurable
probability space: in particular, this theorem does not silently replace infinite
random tapes by finite random seeds. Measurability of the occupancy events is
explicit. No independence between graph-derived IDs and the graph is postulated.
-/

open scoped BigOperators
open MeasureTheory

namespace MISLocal
noncomputable section

theorem average_fixed_tape_bound
    {Ω W : Type*} [Fintype Ω] [MeasurableSpace W]
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (B : Ω → Set W) (hB : ∀ g, MeasurableSet (B g)) (β : ℝ)
    (hfixed : ∀ w, μ.prob (fun g => w ∈ B g) ≤ β) :
    μ.expect (fun g => ν.real (B g)) ≤ β := by
  classical
  have hI (g : Ω) : Integrable (fun w => bit (w ∈ B g)) ν := by
    simpa [bit, Set.indicator] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : W => (1 : ℝ)) ν).indicator (hB g)
  have hval (g : Ω) : (∫ w, bit (w ∈ B g) ∂ν) = ν.real (B g) := by
    simpa [bit, Set.indicator] using
      (integral_indicator_const (μ := ν) (1 : ℝ) (hB g))
  have hi : Integrable (fun w => μ.prob (fun g => w ∈ B g)) ν := by
    exact integrable_finset_sum _ (fun g _ => (hI g).const_mul (μ.weight g))
  have heq : (∫ w, μ.prob (fun g => w ∈ B g) ∂ν) =
      μ.expect (fun g => ν.real (B g)) := by
    unfold FiniteProb.prob FiniteProb.expect
    rw [integral_finset_sum _ (fun g _ => (hI g).const_mul (μ.weight g))]
    simp only [integral_const_mul, hval]
  rw [← heq]
  calc
    _ ≤ ∫ _ : W, β ∂ν := integral_mono hi (integrable_const β) hfixed
    _ = β := by simp

end
end MISLocal


/- ===== Source: MISLocal/InfiniteTapes.lean ===== -/

/-!
# Reindexing independent, possibly infinite random tapes

Only the vertex and identifier index sets are finite. `Tape` is any measurable
space with a probability measure. The theorem preserves the full product measure,
so it establishes joint independence, not just correct marginal distributions.
-/

open MeasureTheory

namespace MISLocal
noncomputable section

theorem tape_reindex_measurePreserving {V ID Tape : Type*}
    [Fintype V] [Fintype ID] [MeasurableSpace Tape]
    (ρ : Measure Tape) [IsProbabilityMeasure ρ] (ids : V ≃ ID) :
    MeasurePreserving (reindexTapes (Tape := Tape) ids)
      (Measure.pi (fun _ : ID => ρ)) (Measure.pi (fun _ : V => ρ)) := by
  convert measurePreserving_piCongrLeft (fun _ : V => ρ) ids.symm using 1
  funext W v
  simp [reindexTapes, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft']

/-- For each fixed graph, a graph-dependent legal ID completion still preserves
the product tape distribution. `ids` has no tape-table argument. -/
theorem graph_dependent_tape_reindex {Ω V ID Tape : Type*}
    [Fintype V] [Fintype ID] [MeasurableSpace Tape]
    (ρ : Measure Tape) [IsProbabilityMeasure ρ] (ids : Ω → V ≃ ID) (g : Ω) :
    (Measure.pi (fun _ : ID => ρ)).map (reindexTapes (Tape := Tape) (ids g)) =
      Measure.pi (fun _ : V => ρ) :=
  (tape_reindex_measurePreserving ρ (ids g)).map_eq

end
end MISLocal


/- ===== Source: MISLocal/Obstruction.lean ===== -/

/-!
# The generic finite obstruction

This module proves the probability-transfer argument. `hsimulation` is a
hypothesis saying that a supplied candidate process matches the real algorithm
on the closed neighborhood of C when local IDs are unique. Deriving this from
LOCAL transition rules is done in the concrete reduction modules. Here
`hfixed` is a per-fixed-table bound. The anonymous occupancy and concrete
reduction modules discharge it for the supplied uniform program.

These hypotheses are parameters of the theorem, never new axioms or hidden
fields of a definition of "LOCAL algorithm".
-/

open MeasureTheory

namespace MISLocal
noncomputable section

variable {Ω W V : Type*} [Fintype Ω] [MeasurableSpace W]

/-- Transfer of occupancy, with the same explicit simulation interface. -/
theorem occupancy_transfer
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (G : Ω → SimpleGraph V) (C : Set V)
    (output candidates : Ω → W → Set V) (uniqueIDs : Ω → Prop)
    (ε δ β : ℝ) (hε : 0 ≤ ε)
    (hcollision : μ.prob (fun g => ¬uniqueIDs g) ≤ δ)
    (hcorrect : ∀ g, ν.real {w | ¬(G g).IsIndepSet (output g w)} ≤ ε)
    (hsimulation : ∀ g, uniqueIDs g → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (G g).Adj v x → (x ∈ candidates g w ↔ x ∈ output g w))
    (hmeas : ∀ g, MeasurableSet {w | Occupies C (repair (G g) (candidates g w))})
    (hfixed : ∀ w,
      μ.prob (fun g => Occupies C (repair (G g) (candidates g w))) ≤ β) :
    μ.expect (fun g => ν.real {w | Occupies C (output g w)}) ≤ β + ε + δ := by
  classical
  let B : Ω → Set W := fun g => {w | Occupies C (repair (G g) (candidates g w))}
  have hpoint (g : Ω) : ν.real {w | Occupies C (output g w)} ≤
      ν.real (B g) + ε + bit (¬uniqueIDs g) := by
    by_cases hu : uniqueIDs g
    · have hsub : {w | Occupies C (output g w)} ⊆
          B g ∪ {w | ¬(G g).IsIndepSet (output g w)} := by
        intro w hw
        by_cases hi : (G g).IsIndepSet (output g w)
        · exact Or.inl ((repair_occupancy_agrees (G g) hi
            (hsimulation g hu w)).mpr hw)
        · exact Or.inr hi
      have hbound := (measureReal_mono (μ := ν) hsub).trans
        (measureReal_union_le (B g) {w | ¬(G g).IsIndepSet (output g w)})
      have hc := hcorrect g
      simp only [bit, not_true_eq_false, hu, if_false, add_zero]
      linarith
    · have hnonneg : 0 ≤ ν.real (B g) := measureReal_nonneg
      have hupper : ν.real {w | Occupies C (output g w)} ≤ 1 := measureReal_le_one
      simp only [bit, if_pos hu]
      linarith
  have hmean := μ.expect_mono hpoint
  rw [μ.expect_add, μ.expect_add, μ.expect_const] at hmean
  have hupper : μ.expect (fun g => ν.real (B g)) ≤ β :=
    average_fixed_tape_bound μ ν B hmeas β hfixed
  change μ.expect (fun g => ν.real {w | Occupies C (output g w)}) ≤
    μ.expect (fun g => ν.real (B g)) + ε + μ.prob (fun g => ¬uniqueIDs g) at hmean
  linarith

/-- Necessary quantitative condition, allowing arbitrarily long random tapes. -/
theorem finite_obstruction
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (G : Ω → SimpleGraph V) (C : Set V)
    (output candidates : Ω → W → Set V) (uniqueIDs : Ω → Prop)
    (ε δ γ β : ℝ) (hε : ε ≤ 1)
    (hcollision : μ.prob (fun g => ¬uniqueIDs g) ≤ δ)
    (hdomination : μ.prob (fun g => ExternallyDominatable (G g) C) ≤ γ)
    (hcorrect : ∀ g,
      1 - ε ≤ ν.real {w | Maximal (G g).IsIndepSet (output g w)})
    (hsimulation : ∀ g, uniqueIDs g → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (G g).Adj v x → (x ∈ candidates g w ↔ x ∈ output g w))
    (hmeas : ∀ g, MeasurableSet {w | Occupies C (repair (G g) (candidates g w))})
    (hfixed : ∀ w,
      μ.prob (fun g => Occupies C (repair (G g) (candidates g w))) ≤ β) :
    (1 - ε) * (1 - δ - γ) ≤ β := by
  classical
  let good : Ω → Prop := fun g => uniqueIDs g ∧ ¬ExternallyDominatable (G g) C
  let B : Ω → Set W := fun g => {w | Occupies C (repair (G g) (candidates g w))}
  have hlower : 1 - δ - γ ≤ μ.prob good := by
    have hi := μ.prob_and_lower uniqueIDs
      (fun g => ¬ExternallyDominatable (G g) C)
    rw [μ.prob_not] at hi
    have hu := μ.prob_not uniqueIDs
    dsimp [good]
    linarith
  have hpoint : ∀ g, (1 - ε) * bit (good g) ≤ ν.real (B g) := by
    intro g
    by_cases hg : good g
    · have hsub : {w | Maximal (G g).IsIndepSet (output g w)} ⊆ B g := by
        intro w hw
        have hoc : Occupies C (output g w) :=
          maximal_occupies_of_not_externally_dominatable (G g) hg.2 hw
        exact (repair_occupancy_agrees (G g) hw.1
          (hsimulation g hg.1 w)).mpr hoc
      simpa [bit, hg] using (hcorrect g).trans (measureReal_mono hsub)
    · simp [bit, hg, measureReal_nonneg]
  have hmean := μ.expect_mono hpoint
  rw [μ.expect_mul] at hmean
  have hupper : μ.expect (fun g => ν.real (B g)) ≤ β :=
    average_fixed_tape_bound μ ν B hmeas β hfixed
  calc
    (1 - ε) * (1 - δ - γ) ≤ (1 - ε) * μ.prob good :=
      mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hε)
    _ ≤ μ.expect (fun g => ν.real (B g)) := hmean
    _ ≤ β := hupper

end
end MISLocal


/- ===== Source: MISLocal/Numerics.lean ===== -/

/-!
# Numerical consequences and subtraction guardrails

These are generic scalar consequences. The finite skeleton construction,
parameter estimates and full asymptotic conclusion are supplied in the
FiniteRegularSkeleton, PowerSize and AsymptoticLocalLowerBound modules.
-/

namespace MISLocal
noncomputable section

def occupancyCap (r : ℕ) (D : ℝ) : ℝ := min 1 (5000 * (r : ℝ) * Real.log D / D)

theorem obstruction_at_least_half {ε δ γ : ℝ}
    (hε : ε ≤ 1 / 3) (herrors : δ + γ ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ (1 - ε) * (1 - δ - γ) := by
  have h1 : (2 / 3 : ℝ) ≤ 1 - ε := by linarith
  have h2 : (3 / 4 : ℝ) ≤ 1 - δ - γ := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- Round lower bound in the degree parameter. The subtraction is in ℝ. -/
theorem degree_round_lower_bound {T : ℕ} {D ε δ γ : ℝ}
    (hD : 1 < D) (hε : ε ≤ 1 / 3) (herrors : δ + γ ≤ 1 / 4)
    (hobstruction : (1 - ε) * (1 - δ - γ) ≤ occupancyCap (T + 3) D) :
    D / (10000 * Real.log D) - 3 ≤ (T : ℝ) := by
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hcap : (1 / 2 : ℝ) ≤ 5000 * ((T : ℝ) + 3) * Real.log D / D := by
    have h := (obstruction_at_least_half hε herrors).trans hobstruction
    exact h.trans (by simp only [occupancyCap, Nat.cast_add, Nat.cast_ofNat]; exact min_le_right _ _)
  have hmul := (le_div_iff₀ hD0).mp hcap
  have hden : 0 < 10000 * Real.log D := by positivity
  have hratio : D / (10000 * Real.log D) ≤ (T : ℝ) + 3 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

/-- The explicit 100000 constant follows from the finite obstruction and these
stated degree/size estimates. Establishing the estimates for all large n, and
constructing the required skeletons, are outside this theorem. -/
theorem size_round_lower_bound {T : ℕ} {D n ε δ γ : ℝ}
    (hD : 1 < D)
    (hDlower : Real.log n / 5 ≤ D)
    (hDupper : D ≤ Real.log n)
    (hlarge : 3 ≤ Real.log n / (100000 * Real.log (Real.log n)))
    (hε : ε ≤ 1 / 3) (herrors : δ + γ ≤ 1 / 4)
    (hobstruction : (1 - ε) * (1 - δ - γ) ≤ occupancyCap (T + 3) D) :
    Real.log n / (100000 * Real.log (Real.log n)) ≤ (T : ℝ) := by
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hn1 : 1 < Real.log n := lt_of_lt_of_le hD hDupper
  have hlogn : 0 < Real.log n := lt_trans zero_lt_one hn1
  have hloglog : 0 < Real.log (Real.log n) := Real.log_pos hn1
  have hlogs : Real.log D ≤ Real.log (Real.log n) :=
    Real.log_le_log (lt_trans zero_lt_one hD) hDupper
  have hbase := degree_round_lower_bound hD hε herrors hobstruction
  have hfrac : 2 * (Real.log n / (100000 * Real.log (Real.log n))) ≤
      D / (10000 * Real.log D) := by
    calc
      _ = (Real.log n / 5) / (10000 * Real.log (Real.log n)) := by ring
      _ ≤ D / (10000 * Real.log (Real.log n)) :=
        div_le_div_of_nonneg_right hDlower (by positivity)
      _ ≤ D / (10000 * Real.log D) :=
        div_le_div_of_nonneg_left (le_of_lt (lt_trans zero_lt_one hD))
          (by positivity) (by nlinarith)
  linarith

/-- The paper's local-collision numerator, with no truncated subtraction. -/
theorem collision_numerator_nonnegative (L : ℕ) :
    0 ≤ (L : ℝ) * ((L : ℝ) - 1) := by
  cases L with
  | zero => norm_num
  | succ L => have h : (0 : ℝ) ≤ L := Nat.cast_nonneg L; push_cast; nlinarith

/-- Casting a genuine natural difference needs the displayed order hypothesis. -/
theorem cast_padding {n k N : ℕ} (hfit : k * N ≤ n) :
    ((n - k * N : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) * (N : ℝ) := by
  rw [Nat.cast_sub hfit, Nat.cast_mul]

end
end MISLocal


/- ===== Source: MISLocal/ConditionalMain.lean ===== -/

/-!
# A checked conditional implication, NOT the full LOCAL lower bound

This combines the verified graph/probability reduction with the verified
numerical estimates. Its parameters display the remaining mathematical work:
the concrete construction must establish `hcollision`, `hdomination`,
`hsimulation`, `hfixed`, the size/degree estimates, and event measurability.
This is the legacy conditional wrapper. `GraphTapeReduction.lean` supplies a
new finite obstruction deriving the occupancy premise from the proved
`graph_occupancy` theorem, while keeping the other model obligations explicit.
-/

open MeasureTheory

namespace MISLocal
noncomputable section

theorem conditional_round_lower_bound
    {Ω W V : Type*} [Fintype Ω] [Fintype V] [MeasurableSpace W]
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (G : Ω → SimpleGraph V) (C : Set V)
    (output candidates : Ω → W → Set V) (uniqueIDs : Ω → Prop)
    (T : ℕ) (D ε δ γ : ℝ)
    (hD : 1 < D) (hDlower : Real.log (Fintype.card V : ℝ) / 5 ≤ D)
    (hDupper : D ≤ Real.log (Fintype.card V : ℝ))
    (hlarge : 3 ≤ Real.log (Fintype.card V : ℝ) /
      (100000 * Real.log (Real.log (Fintype.card V : ℝ))))
    (hε : ε ≤ 1 / 3) (herrors : δ + γ ≤ 1 / 4)
    (hcollision : μ.prob (fun g => ¬uniqueIDs g) ≤ δ)
    (hdomination : μ.prob (fun g => ExternallyDominatable (G g) C) ≤ γ)
    (hcorrect : ∀ g,
      1 - ε ≤ ν.real {w | Maximal (G g).IsIndepSet (output g w)})
    (hsimulation : ∀ g, uniqueIDs g → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (G g).Adj v x → (x ∈ candidates g w ↔ x ∈ output g w))
    (hmeas : ∀ g, MeasurableSet {w | Occupies C (repair (G g) (candidates g w))})
    (hfixed : ∀ w,
      μ.prob (fun g => Occupies C (repair (G g) (candidates g w))) ≤
        occupancyCap (T + 3) D) :
    Real.log (Fintype.card V : ℝ) /
      (100000 * Real.log (Real.log (Fintype.card V : ℝ))) ≤ (T : ℝ) := by
  apply size_round_lower_bound hD hDlower hDupper hlarge hε herrors
  exact finite_obstruction μ ν G C output candidates uniqueIDs ε δ γ
    (occupancyCap (T + 3) D) (by linarith) hcollision hdomination hcorrect
    hsimulation hmeas hfixed

end
end MISLocal


/- ===== Source: MISLocal/Entropy.lean ===== -/

/-!
# Finite Shannon entropy and a zero-event relative-entropy bound

All sums and subtractions take place in `ℝ`. Relative entropy below is a
real-valued sum: its inequalities ALWAYS require explicit support domination.
This is essential because Lean defines `Real.log 0 = 0`.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem weight_le_one (μ : FiniteProb Ω) (ω : Ω) : μ.weight ω ≤ 1 := by
  rw [← μ.total]
  exact Finset.single_le_sum (fun i _ => μ.nonneg i) (Finset.mem_univ ω)

def pointMass (a : Ω) : FiniteProb Ω where
  weight ω := bit (ω = a)
  nonneg ω := bit_nonneg _
  total := by simp [bit]

@[simp] theorem pointMass_expect (a : Ω) (f : Ω → ℝ) :
    (pointMass a).expect f = f a := by simp [pointMass, expect, bit]

@[simp] theorem pointMass_prob (a : Ω) (E : Ω → Prop) :
    (pointMass a).prob E = bit (E a) := pointMass_expect a _

def map (μ : FiniteProb Ω) (X : Ω → A) : FiniteProb A where
  weight a := μ.prob (fun ω => X ω = a)
  nonneg a := μ.prob_nonneg _
  total := by
    simp only [prob, expect]
    rw [Finset.sum_comm]
    simp [bit, μ.total]

theorem expect_map (μ : FiniteProb Ω) (X : Ω → A) (f : A → ℝ) :
    (μ.map X).expect f = μ.expect (fun ω => f (X ω)) := by
  simp only [expect, map, prob, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [bit]

theorem prob_map (μ : FiniteProb Ω) (X : Ω → A) (p : A → Prop) :
    (μ.map X).prob p = μ.prob (fun ω => p (X ω)) :=
  μ.expect_map X (fun a => bit (p a))

theorem map_weight_pos (μ : FiniteProb Ω) (X : Ω → A) {ω : Ω}
    (hω : 0 < μ.weight ω) : 0 < (μ.map X).weight (X ω) := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun v => μ.weight v * bit (X v = X ω))
    (fun v _ => mul_nonneg (μ.nonneg v) (bit_nonneg _)) (Finset.mem_univ ω)
  change μ.weight ω * bit (X ω = X ω) ≤ (μ.map X).weight (X ω) at h
  simp only [bit, ite_true, mul_one] at h
  exact lt_of_lt_of_le hω h

def entropy (μ : FiniteProb Ω) : ℝ := ∑ ω, Real.negMulLog (μ.weight ω)

def entropyOf (μ : FiniteProb Ω) (X : Ω → A) : ℝ := (μ.map X).entropy

def condEntropy (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) : ℝ :=
  μ.entropyOf (fun ω => (X ω, Y ω)) - μ.entropyOf Y

theorem entropy_nonneg (μ : FiniteProb Ω) : 0 ≤ μ.entropy :=
  Finset.sum_nonneg (fun ω _ => Real.negMulLog_nonneg (μ.nonneg ω) (μ.weight_le_one ω))

theorem entropyOf_eq_expect (μ : FiniteProb Ω) (X : Ω → A) :
    μ.entropyOf X = μ.expect (fun ω => -Real.log ((μ.map X).weight (X ω))) := by
  rw [← μ.expect_map X (fun a => -Real.log ((μ.map X).weight a))]
  simp [entropyOf, entropy, expect, Real.negMulLog, mul_neg]

theorem entropyOf_congr (μ : FiniteProb Ω) {X Y : Ω → A} (h : ∀ ω, X ω = Y ω) :
    μ.entropyOf X = μ.entropyOf Y := by
  congr 1
  exact funext h

/-- An explicit support condition, not implicit use of extended-real infinity. -/
def Dominated (P Q : FiniteProb Ω) : Prop :=
  ∀ ω, 0 < P.weight ω → 0 < Q.weight ω

def kl (P Q : FiniteProb Ω) : ℝ :=
  ∑ ω, P.weight ω * (Real.log (P.weight ω) - Real.log (Q.weight ω))

end FiniteProb

/-- Pointwise Gibbs inequality, including the zero-mass case. -/
theorem gibbs_term {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) :
    p - q ≤ p * (Real.log p - Real.log q) := by
  by_cases hp0 : p = 0
  · simp [hp0, hq]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' := hs hp'
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq' hp')
  rw [Real.log_div (ne_of_gt hq') hp0] at hlog
  have h := mul_le_mul_of_nonneg_left hlog hp
  field_simp at h
  nlinarith

namespace FiniteProb

variable {Ω : Type*} [Fintype Ω]

theorem kl_nonneg (P Q : FiniteProb Ω) (h : P.Dominated Q) : 0 ≤ P.kl Q := by
  have hs := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) =>
    gibbs_term (P.nonneg ω) (Q.nonneg ω) (h ω))
  simpa [kl, Finset.sum_sub_distrib, P.total, Q.total] using hs

/-- A zero-probability event has zero mass at each of its points. -/
theorem weight_eq_zero_of_prob_zero (P : FiniteProb Ω) (E : Ω → Prop)
    (hE : P.prob E = 0) {ω : Ω} (hω : E ω) : P.weight ω = 0 := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun v => P.weight v * bit (E v))
    (fun v _ => mul_nonneg (P.nonneg v) (bit_nonneg _)) (Finset.mem_univ ω)
  change P.weight ω * bit (E ω) ≤ P.prob E at h
  simp only [bit, if_pos hω, mul_one, hE] at h
  exact le_antisymm h (P.nonneg ω)

/-- The only change-of-distribution estimate needed for zero-conflict ancestors.
No square roots, strict positive-probability convention, or Jensen limit is used. -/
theorem zero_event_le_kl (P Q : FiniteProb Ω) (h : P.Dominated Q)
    (E : Ω → Prop) (hE : P.prob E = 0) : Q.prob E ≤ P.kl Q := by
  have hpoint : ∀ ω, P.weight ω - Q.weight ω * bit (¬ E ω) ≤
      P.weight ω * (Real.log (P.weight ω) - Real.log (Q.weight ω)) := by
    intro ω
    by_cases he : E ω
    · have hp := P.weight_eq_zero_of_prob_zero E hE he
      simp [hp, bit, he]
    · simpa [bit, he] using gibbs_term (P.nonneg ω) (Q.nonneg ω) (h ω)
  have hs := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hpoint ω)
  change (∑ ω, (P.weight ω - Q.weight ω * bit (¬E ω))) ≤ P.kl Q at hs
  rw [Finset.sum_sub_distrib, P.total] at hs
  change 1 - Q.prob (fun ω => ¬E ω) ≤ P.kl Q at hs
  rw [Q.prob_not] at hs
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/EntropyBudget.lean ===== -/

/-!
# Rare-output entropy and the first-failure mass budget

`massBudget m p` is the continuous-at-zero expression `p * log (e*m/p)`.
It is defined as `p * (1 + log m) + negMulLog p`, so its zero case does
not depend on a division convention. The budget for a partition of the
occupied mass is proved here, not postulated as a property of algorithms.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def massBudget (m p : ℝ) : ℝ := p * (1 + Real.log m) + Real.negMulLog p

@[simp] theorem massBudget_zero (m : ℝ) : massBudget m 0 = 0 := by
  simp [massBudget]

theorem massBudget_eq {m p : ℝ} (hm : 0 < m) (hp : 0 < p) :
    massBudget m p = p * Real.log (Real.exp 1 * m / p) := by
  rw [Real.log_div (mul_ne_zero (ne_of_gt (Real.exp_pos _)) (ne_of_gt hm))
    (ne_of_gt hp), Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hm),
    Real.log_exp]
  simp [massBudget, Real.negMulLog]
  ring

/-- A tangent-line proof of the finite entropy bound; zero coordinates are allowed. -/
theorem negMulLog_tangent {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    Real.negMulLog x ≤ -x * Real.log a + a - x := by
  have h := gibbs_term hx (le_of_lt ha) (fun _ => ha)
  simp only [Real.negMulLog]
  nlinarith

/-- Entropy of arbitrary nonnegative masses, without assuming their sum is one. -/
theorem sum_negMulLog_le {I : Type*} [Fintype I] [Nonempty I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, Real.negMulLog (x i)) ≤
      Real.negMulLog (∑ i, x i) + (∑ i, x i) * Real.log (Fintype.card I) := by
  let p := ∑ i, x i
  have hp : 0 ≤ p := Finset.sum_nonneg (fun i _ => hx i)
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  by_cases hp0 : p = 0
  · have hz (i : I) : x i = 0 := by
      have hi := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      change x i ≤ p at hi
      exact le_antisymm (hp0 ▸ hi) (hx i)
    simp [hz]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    negMulLog_tangent (hx i) (div_pos hp' hc))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hs
  change (∑ i, Real.negMulLog (x i)) ≤
    -p * Real.log (p / Fintype.card I) + Fintype.card I * (p / Fintype.card I) - p at hs
  rw [Real.log_div hp0 (ne_of_gt hc), mul_div_cancel₀ _ (ne_of_gt hc)] at hs
  change (∑ i, Real.negMulLog (x i)) ≤ Real.negMulLog p + p * Real.log (Fintype.card I)
  simp only [Real.negMulLog] at hs ⊢
  nlinarith

theorem FiniteProb.entropy_le_log_card {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (μ : FiniteProb Ω) : μ.entropy ≤ Real.log (Fintype.card Ω) := by
  simpa [FiniteProb.entropy, μ.total] using sum_negMulLog_le μ.weight μ.nonneg

/-- The r disjoint first-failure/survivor masses cost only log r, not r. -/
theorem sum_massBudget_le {I : Type*} [Fintype I] [Nonempty I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) {m : ℝ} (hm : 0 < m) :
    (∑ i, massBudget m (x i)) ≤ massBudget (m * Fintype.card I) (∑ i, x i) := by
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs := sum_negMulLog_le x hx
  simp only [massBudget, Finset.sum_add_distrib, ← Finset.sum_mul,
    Real.log_mul (ne_of_gt hm) hc]
  nlinarith

/-- Monotonicity on probability masses, with its scale hypothesis explicit. -/
theorem massBudget_mono {m x y : ℝ} (hm : 1 ≤ m)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : massBudget m x ≤ massBudget m y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  by_cases hyz : y = 0
  · have hxz : x = 0 := le_antisymm (hyz ▸ hxy) hx
    simp [hxz, hyz]
  have hyp : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyz)
  have ht := negMulLog_tangent hx hyp
  have hlogy : Real.log y ≤ 0 := Real.log_nonpos hy0 hy
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hprod : 0 ≤ (y - x) * (Real.log m - Real.log y) :=
    mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr (hlogy.trans hlogm))
  simp only [massBudget, Real.negMulLog] at ht ⊢
  nlinarith

/-- Quantitative sum of the individual direct-projection conflict bounds. -/
theorem joint_conflict_budget {I : Type*} [Fintype I] [Nonempty I]
    (x w : I → ℝ) {D m p : ℝ}
    (hD : 0 < D) (hm : 1 ≤ m) (hx : ∀ i, 0 ≤ x i)
    (hp : p ≤ 1) (hmass : ∑ i, x i ≤ p)
    (hw : ∀ i, w i ≤ 2 * massBudget m (x i) / D) :
    (∑ i, w i) ≤ 2 * massBudget (m * Fintype.card I) p / D := by
  have hc : (1 : ℝ) ≤ Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hm' : 1 ≤ m * Fintype.card I := one_le_mul_of_one_le_of_one_le hm hc
  have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
  have hb := (sum_massBudget_le x hx (lt_of_lt_of_le zero_lt_one hm)).trans
    (massBudget_mono hm' hsum hmass hp)
  calc
    _ ≤ ∑ i, 2 * massBudget m (x i) / D := Finset.sum_le_sum (fun i _ => hw i)
    _ = 2 * (∑ i, massBudget m (x i)) / D := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hD.le

end
end MISLocal


/- ===== Source: MISLocal/ConditionalEntropy.lean ===== -/

/-!
# Conditional entropy for finite random variables

Conditional entropy is joint entropy minus the conditioning entropy. The
submodular inequality and "conditioning reduces entropy" are derived from
Gibbs' inequality for the actual finite distributions, not assumed.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

theorem expect_congr_on_support (μ : FiniteProb Ω) (f g : Ω → ℝ)
    (h : ∀ ω, 0 < μ.weight ω → f ω = g ω) : μ.expect f = μ.expect g := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hz : μ.weight ω = 0
  · simp [hz]
  · rw [h ω (lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hz))]

theorem expect_mono_on_support (μ : FiniteProb Ω) (f g : Ω → ℝ)
    (h : ∀ ω, 0 < μ.weight ω → f ω ≤ g ω) : μ.expect f ≤ μ.expect g := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hz : μ.weight ω = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left
      (h ω (lt_of_le_of_ne (μ.nonneg ω) (Ne.symm hz))) (μ.nonneg ω)

theorem entropyOf_comp_injective (μ : FiniteProb Ω) (X : Ω → A)
    (f : A → B) (hf : Function.Injective f) :
    μ.entropyOf (fun ω => f (X ω)) = μ.entropyOf X := by
  rw [entropyOf_eq_expect, entropyOf_eq_expect]
  apply μ.expect_congr
  intro ω
  apply congrArg (fun t : ℝ => -Real.log t)
  exact μ.prob_congr (fun v => hf.eq_iff)

theorem entropy_pair_comm (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    μ.entropyOf (fun ω => (X ω, Y ω)) = μ.entropyOf (fun ω => (Y ω, X ω)) := by
  exact (μ.entropyOf_comp_injective (fun ω => (X ω, Y ω))
    (Equiv.prodComm A B) (Equiv.prodComm A B).injective).symm

theorem entropy_pair_assoc (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    μ.entropyOf (fun ω => ((X ω, Y ω), Z ω)) =
      μ.entropyOf (fun ω => (X ω, Y ω, Z ω)) := by
  exact (μ.entropyOf_comp_injective (fun ω => ((X ω, Y ω), Z ω))
    (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C).injective).symm

theorem entropy_deterministic_pair (μ : FiniteProb Ω) (Y : Ω → B) (f : B → A) :
    μ.entropyOf (fun ω => (f (Y ω), Y ω)) = μ.entropyOf Y := by
  apply μ.entropyOf_comp_injective Y (fun b => (f b, b))
  intro b c h
  exact congrArg Prod.snd h

theorem condEntropy_deterministic (μ : FiniteProb Ω) (Y : Ω → B) (f : B → A) :
    μ.condEntropy (fun ω => f (Y ω)) Y = 0 := by
  simp [condEntropy, entropy_deterministic_pair]

theorem pair_weight_le_right (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B)
    (a : A) (b : B) : (μ.map (fun ω => (X ω, Y ω))).weight (a,b) ≤
      (μ.map Y).weight b := by
  exact μ.prob_mono (fun _ h => congrArg Prod.snd h)

theorem pair_sum_left (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (b : B) :
    (∑ a, (μ.map (fun ω => (X ω, Y ω))).weight (a,b)) = (μ.map Y).weight b := by
  simp only [map, prob, expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : Y ω = b <;> simp [bit, Prod.ext_iff, h]

theorem pair_sum_right (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (a : A) :
    (∑ b, (μ.map (fun ω => (X ω, Y ω))).weight (a,b)) = (μ.map X).weight a := by
  simp only [map, prob, expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : X ω = a <;> simp [bit, Prod.ext_iff, h]

theorem condEntropy_nonneg (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    0 ≤ μ.condEntropy X Y := by
  unfold condEntropy
  apply sub_nonneg.mpr
  rw [entropyOf_eq_expect, entropyOf_eq_expect]
  apply μ.expect_mono_on_support
  intro ω hω
  exact neg_le_neg (Real.log_le_log (μ.map_weight_pos (fun v => (X v, Y v)) hω)
    (μ.pair_weight_le_right X Y (X ω) (Y ω)))

/-- Conditional product distribution: X and Z are independent given Y.
Zero-probability Y fibers contribute exactly zero. -/
def conditionalProduct (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    FiniteProb (A × B × C) where
  weight abc := (μ.map (fun ω => (X ω, Y ω))).weight (abc.1, abc.2.1) *
    (μ.map (fun ω => (Y ω, Z ω))).weight (abc.2.1, abc.2.2) /
      (μ.map Y).weight abc.2.1
  nonneg abc := div_nonneg (mul_nonneg (μ.prob_nonneg _) (μ.prob_nonneg _))
    (μ.prob_nonneg _)
  total := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc
      _ = ∑ b, (μ.map Y).weight b := by
        apply Finset.sum_congr rfl
        intro b _
        simp only [← Finset.sum_div, ← Finset.mul_sum, μ.pair_sum_right Y Z,
          ← Finset.sum_mul, μ.pair_sum_left X Y]
        by_cases hb : (μ.map Y).weight b = 0
        · simp [hb]
        · exact mul_div_cancel_right₀ _ hb
      _ = 1 := (μ.map Y).total

theorem dominated_conditionalProduct (μ : FiniteProb Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    (μ.map (fun ω => (X ω, Y ω, Z ω))).Dominated (μ.conditionalProduct X Y Z) := by
  intro abc h
  have hxy : 0 < (μ.map (fun ω => (X ω, Y ω))).weight (abc.1,abc.2.1) :=
    lt_of_lt_of_le h (μ.prob_mono (fun _ he =>
      congrArg (fun p : A × B × C => (p.1,p.2.1)) he))
  have hyz : 0 < (μ.map (fun ω => (Y ω, Z ω))).weight abc.2 :=
    lt_of_lt_of_le h (μ.prob_mono (fun _ he => congrArg Prod.snd he))
  have hy : 0 < (μ.map Y).weight abc.2.1 :=
    lt_of_lt_of_le hxy (μ.pair_weight_le_right X Y abc.1 abc.2.1)
  exact div_pos (mul_pos hxy hyz) hy

/-- An exact entropy identity for the relative entropy of the conditional product. -/
theorem kl_conditionalProduct (μ : FiniteProb Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    (μ.map (fun ω => (X ω, Y ω, Z ω))).kl (μ.conditionalProduct X Y Z) =
      μ.entropyOf (fun ω => (X ω,Y ω)) + μ.entropyOf (fun ω => (Y ω,Z ω)) -
        μ.entropyOf Y - μ.entropyOf (fun ω => (X ω,Y ω,Z ω)) := by
  change (μ.map (fun ω => (X ω, Y ω, Z ω))).expect _ = _
  rw [μ.expect_map]
  simp only [entropyOf_eq_expect, ← expect_add, ← expect_sub]
  apply μ.expect_congr_on_support
  intro ω hω
  have hxy := ne_of_gt (μ.map_weight_pos (fun v => (X v,Y v)) hω)
  have hyz := ne_of_gt (μ.map_weight_pos (fun v => (Y v,Z v)) hω)
  have hy := ne_of_gt (μ.map_weight_pos Y hω)
  change Real.log _ - Real.log (_ * _ / _) = _
  rw [Real.log_div (mul_ne_zero hxy hyz) hy, Real.log_mul hxy hyz]
  ring

theorem entropy_submodular (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    μ.entropyOf Y + μ.entropyOf (fun ω => (X ω,Y ω,Z ω)) ≤
      μ.entropyOf (fun ω => (X ω,Y ω)) + μ.entropyOf (fun ω => (Y ω,Z ω)) := by
  have h := FiniteProb.kl_nonneg _ _ (μ.dominated_conditionalProduct X Y Z)
  rw [μ.kl_conditionalProduct] at h
  linarith

theorem conditioning_reduces (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    μ.condEntropy X (fun ω => (Y ω,Z ω)) ≤ μ.condEntropy X Y := by
  have h := μ.entropy_submodular X Y Z
  simp only [condEntropy]
  linarith

/-- The conditional chain rule is an identity, with no independence assumption. -/
theorem condEntropy_chain (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (Z : Ω → C) :
    μ.condEntropy (fun ω => (X ω,Y ω)) Z =
      μ.condEntropy Y Z + μ.condEntropy X (fun ω => (Y ω,Z ω)) := by
  simp only [condEntropy, μ.entropy_pair_assoc]
  ring

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/EntropyCopying.lean ===== -/

/-!
# The information-copying step used by the tree entropy proof

This is a theorem about actual Shannon entropies of arbitrary finite random
variables. A destination state Y receives W = f(S) from a source edge state S.
The source edge gains no entropy. Each other incident edge gains at most
H(W | Y), exactly offset by the vertex term.

It does not assert that the required copying schedule has been constructed
on the infinite regular tree; that geometric construction remains separate.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C E I : Type*}
  [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype I]

theorem source_edge_copy_entropy (μ : FiniteProb Ω)
    (S : Ω → A) (Y : Ω → B) (f : A → C) :
    μ.entropyOf (fun ω => ((f (S ω), Y ω), S ω)) =
      μ.entropyOf (fun ω => (Y ω, S ω)) := by
  apply μ.entropyOf_comp_injective (fun ω => (Y ω, S ω))
    (fun p : B × A => ((f p.2, p.1), p.2))
  intro p q h
  exact Prod.ext (congrArg (fun t : (C × B) × A => t.1.2) h)
    (congrArg (fun t : (C × B) × A => t.2) h)

theorem other_edge_copy_entropy (μ : FiniteProb Ω)
    (W : Ω → C) (Y : Ω → B) (Z : Ω → E) :
    μ.entropyOf (fun ω => ((W ω,Y ω),Z ω)) - μ.entropyOf (fun ω => (Y ω,Z ω)) ≤
      μ.entropyOf (fun ω => (W ω,Y ω)) - μ.entropyOf Y := by
  rw [μ.entropy_pair_assoc]
  exact μ.conditioning_reduces W Y Z

/-- Exact local change in the edge-minus-vertex entropy potential is nonpositive.
The number of OTHER edges is `card I`; thus on a D-regular tree it is D-1.
There is no natural-number subtraction in this statement. -/
theorem copying_potential_nonincrease (μ : FiniteProb Ω)
    (S : Ω → A) (Y : Ω → B) (f : A → C) (Z : I → Ω → E) :
    (μ.entropyOf (fun ω => ((f (S ω),Y ω),S ω)) -
        μ.entropyOf (fun ω => (Y ω,S ω))) +
      (∑ i, (μ.entropyOf (fun ω => ((f (S ω),Y ω),Z i ω)) -
        μ.entropyOf (fun ω => (Y ω,Z i ω)))) -
      (Fintype.card I : ℝ) *
        (μ.entropyOf (fun ω => (f (S ω),Y ω)) - μ.entropyOf Y) ≤ 0 := by
  rw [μ.source_edge_copy_entropy S Y f, sub_self, zero_add]
  apply sub_nonpos.mpr
  calc
    _ ≤ ∑ _i : I, (μ.entropyOf (fun ω => (f (S ω),Y ω)) - μ.entropyOf Y) := by
      apply Finset.sum_le_sum
      intro i _
      exact μ.other_edge_copy_entropy (fun ω => f (S ω)) Y (Z i)
    _ = _ := by simp [mul_sub]

end FiniteProb

/-- Cancellation of raw-input entropy after the neighborhood counts are known.
The common factor g may be enormous; it cancels identically. -/
theorem raw_tree_entropy_cancellation (D g : ℝ) (h : ℕ) :
    D / 2 * (1 + 2 * ∑ i ∈ Finset.range h, (D-1)^(i+1)) * g -
      (D-1) * (D * ∑ i ∈ Finset.range h, (D-1)^i) * g - D/2*g = 0 := by
  simp only [pow_succ, ← Finset.sum_mul]
  ring

/-- Numerical endpoint of the copying argument, with its schedule inequality
explicit. This is NOT a theorem constructing that schedule on a regular tree. -/
theorem tree_entropy_from_copying_endpoints {D Hvertex Hedge K : ℝ}
    (hcopy : K ≤ D / 2 * Hedge - (D-1) * Hvertex) :
    D / 2 * Hedge ≥ (D-1) * Hvertex + K := by linarith

end
end MISLocal


/- ===== Source: MISLocal/RareEntropy.lean ===== -/

/-! Entropy bounds for a genuinely small support with an additional empty output. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem sum_negMulLog_support_le {A : Type*} [Fintype A]
    (x : A → ℝ) (hx : ∀ a, 0 ≤ x a) (S : Finset A) {m : ℝ}
    (hm : 0 < m) (hcard : (S.card : ℝ) ≤ m)
    (hsupport : ∀ a, a ∉ S → x a = 0) :
    (∑ a, Real.negMulLog (x a)) ≤
      Real.negMulLog (∑ a, x a) + (∑ a, x a) * Real.log m := by
  let p := ∑ a, x a
  have hp : 0 ≤ p := Finset.sum_nonneg (fun a _ => hx a)
  have hsum : (∑ a ∈ S, x a) = p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha
    exact hsupport a ha
  have hentropy : (∑ a ∈ S, Real.negMulLog (x a)) = ∑ a, Real.negMulLog (x a) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha
    simp [hsupport a ha]
  by_cases hp0 : p = 0
  · have hz (a : A) : x a = 0 := by
      have h := Finset.single_le_sum (fun a _ => hx a) (Finset.mem_univ a)
      change x a ≤ p at h
      exact le_antisymm (hp0 ▸ h) (hx a)
    simp [hz]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have ht := Finset.sum_le_sum (s := S) (fun a _ => negMulLog_tangent (hx a) (div_pos hpp hm))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_neg_distrib, Finset.sum_const, nsmul_eq_mul, hsum, hentropy] at ht
  have hc := mul_le_mul_of_nonneg_right hcard (le_of_lt (div_pos hpp hm))
  rw [mul_div_cancel₀ _ (ne_of_gt hm)] at hc
  rw [Real.log_div hp0 (ne_of_gt hm)] at ht
  change (∑ a, Real.negMulLog (x a)) ≤ Real.negMulLog p + p * Real.log m
  simp only [Real.negMulLog] at ht ⊢
  nlinarith

namespace FiniteProb

variable {A : Type*} [Fintype A]

theorem occupied_mass (μ : FiniteProb (Option A)) :
    (∑ a, μ.weight (some a)) = μ.prob (fun a => a ≠ none) := by
  simp [prob, expect, Fintype.sum_option, bit]

theorem empty_mass (μ : FiniteProb (Option A)) :
    μ.weight none = 1 - μ.prob (fun a => a ≠ none) := by
  have ht := μ.total
  rw [Fintype.sum_option, μ.occupied_mass] at ht
  linarith

/-- H(Z) ≤ p log(e m / p), with an explicit nonzero support of at most m labels.
Includes p=0, p=1, and the empty support. -/
theorem rare_entropy_le (μ : FiniteProb (Option A)) (S : Finset A) {m : ℝ}
    (hm : 0 < m) (hcard : (S.card : ℝ) ≤ m)
    (hsupport : ∀ a, a ∉ S → μ.weight (some a) = 0) :
    μ.entropy ≤ massBudget m (μ.prob (fun a => a ≠ none)) := by
  have hs := sum_negMulLog_support_le (fun a => μ.weight (some a))
    (fun a => μ.nonneg _) S hm hcard hsupport
  rw [μ.occupied_mass] at hs
  have he := negMulLog_tangent (μ.nonneg none) (show (0:ℝ) < 1 by norm_num)
  simp only [Real.log_one, mul_zero, neg_zero, zero_add, μ.empty_mass] at he
  unfold entropy
  rw [Fintype.sum_option]
  simp only [massBudget]
  rw [μ.empty_mass]
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/Conditioning.lean ===== -/

/-!
# Finite conditional probabilities, including null fibers

On a null conditioning fiber `given` returns the original distribution.
Its value on such fibers is irrelevant because every identity multiplies it
by the fiber probability. Positivity is explicit whenever a quotient is used.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

def given (μ : FiniteProb Ω) (Y : Ω → B) (b : B) : FiniteProb Ω :=
  if hb : 0 < (μ.map Y).weight b then
    { weight := fun ω => μ.weight ω * bit (Y ω = b) / (μ.map Y).weight b
      nonneg := fun ω => div_nonneg (mul_nonneg (μ.nonneg ω) (bit_nonneg _)) hb.le
      total := by
        rw [← Finset.sum_div]
        change (μ.map Y).weight b / (μ.map Y).weight b = 1
        exact div_self (ne_of_gt hb) }
  else μ

theorem given_weight (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) (ω : Ω) :
    (μ.given Y b).weight ω = μ.weight ω * bit (Y ω = b) / (μ.map Y).weight b := by
  simp [given, hb]

theorem weighted_given_expect (μ : FiniteProb Ω) (Y : Ω → B) (b : B) (f : Ω → ℝ) :
    (μ.map Y).weight b * (μ.given Y b).expect f =
      μ.expect (fun ω => bit (Y ω = b) * f ω) := by
  by_cases hb : 0 < (μ.map Y).weight b
  · simp only [expect, given_weight μ Y b hb, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    field_simp
    ring
  · have hb0 : (μ.map Y).weight b = 0 :=
      le_antisymm (le_of_not_gt hb) ((μ.map Y).nonneg b)
    rw [hb0, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hω : Y ω = b
    · have hz := μ.weight_eq_zero_of_prob_zero (fun ω => Y ω = b) hb0 hω
      simp [hz]
    · simp [bit, hω]

theorem total_conditional_expectation (μ : FiniteProb Ω) (Y : Ω → B) (f : Ω → ℝ) :
    (∑ b, (μ.map Y).weight b * (μ.given Y b).expect f) = μ.expect f := by
  simp only [μ.weighted_given_expect]
  rw [← μ.expect_sum]
  apply μ.expect_congr
  intro ω
  simp [bit]

theorem given_pair_mass (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) (a : A) (b : B)
    (hb : 0 < (μ.map Y).weight b) :
    ((μ.given Y b).map X).weight a =
      (μ.map (fun ω => (X ω,Y ω))).weight (a,b) / (μ.map Y).weight b := by
  change (∑ ω, (μ.given Y b).weight ω * bit (X ω = a)) = _
  simp only [μ.given_weight Y b hb]
  change _ = (∑ ω, μ.weight ω * bit ((X ω,Y ω) = (a,b))) / _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hx : X ω = a <;> by_cases hy : Y ω = b <;>
    simp [bit, Prod.ext_iff, hx, hy]

/-- Conditional entropy equals the average entropy on conditioning fibers. -/
theorem condEntropy_eq_average (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    μ.condEntropy X Y =
      ∑ b, (μ.map Y).weight b * (μ.given Y b).entropyOf X := by
  simp only [entropyOf_eq_expect, μ.weighted_given_expect]
  rw [← μ.expect_sum]
  simp only [condEntropy, entropyOf_eq_expect, ← μ.expect_sub]
  apply μ.expect_congr_on_support
  intro ω hω
  simp only [bit, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hy := μ.map_weight_pos Y hω
  have hxy := μ.map_weight_pos (fun v => (X v,Y v)) hω
  rw [μ.given_pair_mass X Y (X ω) (Y ω) hy,
    Real.log_div (ne_of_gt hxy) (ne_of_gt hy)]
  ring

/-- Jensen's inequality for the continuous rare-output entropy budget. -/
theorem expect_massBudget_le (μ : FiniteProb Ω) (x : Ω → ℝ)
    (hx : ∀ ω, 0 ≤ x ω) (m : ℝ) :
    μ.expect (fun ω => massBudget m (x ω)) ≤ massBudget m (μ.expect x) := by
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := μ.weight) (p := x)
    (fun ω _ => μ.nonneg ω) μ.total (fun ω _ => hx ω)
  simp only [smul_eq_mul] at hj
  simp only [massBudget, expect, mul_add, Finset.sum_add_distrib,
    ← mul_assoc, ← Finset.sum_mul]
  linarith

/-- The support list may depend on the smaller view. Its entropy cost still
depends only on the AVERAGE nonempty-output probability. Null fibers are harmless. -/
theorem conditional_rare_entropy_le (μ : FiniteProb Ω) (X : Ω → Option A)
    (Y : Ω → B) (S : B → Finset A) {m : ℝ} (hm : 0 < m)
    (hcard : ∀ b, ((S b).card : ℝ) ≤ m)
    (hsupport : ∀ b, 0 < (μ.map Y).weight b → ∀ a, a ∉ S b →
      ((μ.given Y b).map X).weight (some a) = 0) :
    μ.condEntropy X Y ≤ massBudget m (μ.prob (fun ω => X ω ≠ none)) := by
  rw [μ.condEntropy_eq_average X Y]
  have hpoint (b : B) : (μ.map Y).weight b * (μ.given Y b).entropyOf X ≤
      (μ.map Y).weight b * massBudget m ((μ.given Y b).prob (fun ω => X ω ≠ none)) := by
    by_cases hb : 0 < (μ.map Y).weight b
    · have h := ((μ.given Y b).map X).rare_entropy_le (S b) hm (hcard b) (hsupport b hb)
      rw [(μ.given Y b).prob_map] at h
      exact mul_le_mul_of_nonneg_left h hb.le
    · have hb0 := le_antisymm (le_of_not_gt hb) ((μ.map Y).nonneg b)
      simp [hb0]
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  have hj := (μ.map Y).expect_massBudget_le
    (fun b => (μ.given Y b).prob (fun ω => X ω ≠ none))
    (fun b => (μ.given Y b).prob_nonneg _) m
  have ht := μ.total_conditional_expectation Y (fun ω => bit (X ω ≠ none))
  change (μ.map Y).expect (fun b => (μ.given Y b).prob (fun ω => X ω ≠ none)) = _ at ht
  rw [ht] at hj
  exact hs.trans hj

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/Projection.lean ===== -/

/-!
# Direct projection onto two smaller views

The reference distribution keeps F and draws the two outputs independently
using their respective smaller-view conditional probabilities. Its relative
entropy is computed exactly. The tree entropy inequality is still an explicit
hypothesis: this module does not replace its missing geometric proof by an axiom.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C Y Z : Type*}
  [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype Y] [Fintype Z]

def projectedPair (μ : FiniteProb Ω) (F : Ω → C) (U : Ω → A) (V : Ω → B)
    (y : C → Y) (z : C → Z) : FiniteProb (C × A × B) where
  weight t := (μ.map F).weight t.1 *
    ((μ.given (fun ω => y (F ω)) (y t.1)).map U).weight t.2.1 *
      ((μ.given (fun ω => z (F ω)) (z t.1)).map V).weight t.2.2
  nonneg t := mul_nonneg (mul_nonneg ((μ.map F).nonneg _)
    (((μ.given _ _).map U).nonneg _)) (((μ.given _ _).map V).nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, FiniteProb.total, mul_one]

theorem dominated_projectedPair (μ : FiniteProb Ω)
    (F : Ω → C) (U : Ω → A) (V : Ω → B) (y : C → Y) (z : C → Z) :
    (μ.map (fun ω => (F ω,U ω,V ω))).Dominated (μ.projectedPair F U V y z) := by
  intro t ht
  have hf : 0 < (μ.map F).weight t.1 :=
    lt_of_lt_of_le ht (μ.prob_mono (fun _ h => congrArg Prod.fst h))
  have huy : 0 < (μ.map (fun ω => (U ω,y (F ω)))).weight (t.2.1,y t.1) :=
    lt_of_lt_of_le ht (μ.prob_mono (fun _ h =>
      congrArg (fun v : C × A × B => (v.2.1,y v.1)) h))
  have hvz : 0 < (μ.map (fun ω => (V ω,z (F ω)))).weight (t.2.2,z t.1) :=
    lt_of_lt_of_le ht (μ.prob_mono (fun _ h =>
      congrArg (fun v : C × A × B => (v.2.2,z v.1)) h))
  have hy := lt_of_lt_of_le huy (μ.pair_weight_le_right U (fun ω => y (F ω)) _ _)
  have hz := lt_of_lt_of_le hvz (μ.pair_weight_le_right V (fun ω => z (F ω)) _ _)
  change 0 < _ * _ * _
  rw [μ.given_pair_mass U _ _ _ hy, μ.given_pair_mass V _ _ _ hz]
  exact mul_pos (mul_pos hf (div_pos huy hy)) (div_pos hvz hz)

theorem kl_projectedPair (μ : FiniteProb Ω)
    (F : Ω → C) (U : Ω → A) (V : Ω → B) (y : C → Y) (z : C → Z) :
    (μ.map (fun ω => (F ω,U ω,V ω))).kl (μ.projectedPair F U V y z) =
      μ.condEntropy U (fun ω => y (F ω)) + μ.condEntropy V (fun ω => z (F ω)) -
        μ.condEntropy (fun ω => (U ω,V ω)) F := by
  change (μ.map (fun ω => (F ω,U ω,V ω))).expect _ = _
  rw [μ.expect_map]
  simp only [condEntropy, μ.entropy_pair_comm (fun ω => (U ω,V ω)) F,
    entropyOf_eq_expect, ← expect_sub, ← expect_add]
  apply μ.expect_congr_on_support
  intro ω hω
  have hf := μ.map_weight_pos F hω
  have hy := μ.map_weight_pos (fun v => y (F v)) hω
  have hz := μ.map_weight_pos (fun v => z (F v)) hω
  have huy := μ.map_weight_pos (fun v => (U v,y (F v))) hω
  have hvz := μ.map_weight_pos (fun v => (V v,z (F v))) hω
  change Real.log _ - Real.log (_ * _ * _) = _
  rw [μ.given_pair_mass U _ _ _ hy, μ.given_pair_mass V _ _ _ hz]
  rw [Real.log_mul (mul_ne_zero (ne_of_gt hf) (ne_of_gt (div_pos huy hy)))
      (ne_of_gt (div_pos hvz hz)),
    Real.log_mul (ne_of_gt hf) (ne_of_gt (div_pos huy hy)),
    Real.log_div (ne_of_gt huy) (ne_of_gt hy),
    Real.log_div (ne_of_gt hvz) (ne_of_gt hz)]
  ring

/-- Arbitrarily many layers may be projected at once. The displayed entropy
inequality is the one missing tree-geometric input, not a definition of a rule. -/
theorem direct_projection_zero_event (μ : FiniteProb Ω)
    (F : Ω → C) (U : Ω → A) (V : Ω → B) (y : C → Y) (z : C → Z)
    (E : C × A × B → Prop) {D K : ℝ} (hD : 0 < D)
    (hsym : μ.condEntropy V (fun ω => z (F ω)) = μ.condEntropy U (fun ω => y (F ω)))
    (htree : (D-1) * μ.condEntropy U (fun ω => y (F ω)) + K ≤
      D/2 * μ.condEntropy (fun ω => (U ω,V ω)) F)
    (hzero : (μ.map (fun ω => (F ω,U ω,V ω))).prob E = 0) :
    (μ.projectedPair F U V y z).prob E ≤
      2 * (μ.condEntropy U (fun ω => y (F ω)) - K) / D := by
  have he := FiniteProb.zero_event_le_kl _ _
    (μ.dominated_projectedPair F U V y z) E hzero
  rw [μ.kl_projectedPair, hsym] at he
  apply (le_div_iff₀ hD).mpr
  have hm := mul_le_mul_of_nonneg_right he hD.le
  nlinarith

/-- The actual projected conflict event is bounded by the rare-output entropy.
Conditional supports, zero conflict, symmetry, and the tree entropy inequality
are each visible premises; no premise states the desired probability bound. -/
theorem direct_projection_rare_bound (μ : FiniteProb Ω)
    (F : Ω → C) (U : Ω → Option A) (V : Ω → Option B) (y : C → Y) (z : C → Z)
    (S : Y → Finset A) (E : C × Option A × Option B → Prop) {D m K : ℝ}
    (hD : 0 < D) (hm : 0 < m) (hK : 0 ≤ K)
    (hcard : ∀ b, ((S b).card : ℝ) ≤ m)
    (hsupport : ∀ b, 0 < (μ.map (fun ω => y (F ω))).weight b → ∀ a, a ∉ S b →
      ((μ.given (fun ω => y (F ω)) b).map U).weight (some a) = 0)
    (hsym : μ.condEntropy V (fun ω => z (F ω)) = μ.condEntropy U (fun ω => y (F ω)))
    (htree : (D-1) * μ.condEntropy U (fun ω => y (F ω)) + K ≤
      D/2 * μ.condEntropy (fun ω => (U ω,V ω)) F)
    (hzero : (μ.map (fun ω => (F ω,U ω,V ω))).prob E = 0) :
    (μ.projectedPair F U V y z).prob E ≤
      2 * massBudget m (μ.prob (fun ω => U ω ≠ none)) / D := by
  have he := μ.direct_projection_zero_event F U V y z E hD hsym htree hzero
  have hs := μ.conditional_rare_entropy_le U (fun ω => y (F ω)) S hm hcard hsupport
  apply he.trans
  apply div_le_div_of_nonneg_right _ hD.le
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/FirstFailure.lean ===== -/

/-!
# Averaging through smaller views and first-failure mass accounting

These are the finite tower/pullout identities used to relate successive
resamplings to restrictions of the original zero-conflict rule. They are
equalities of conditional averages, not of realized resampled outputs.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem expect_mul_given (μ : FiniteProb Ω) (Z : Ω → A) (g : A → ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => g (Z ω) * (μ.given Z (Z ω)).expect f) =
      μ.expect (fun ω => g (Z ω) * f ω) := by
  rw [← μ.expect_map Z (fun a => g a * (μ.given Z a).expect f)]
  change (∑ a, (μ.map Z).weight a * (g a * (μ.given Z a).expect f)) = _
  calc
    _ = ∑ a, g a * μ.expect (fun ω => bit (Z ω = a) * f ω) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← μ.weighted_given_expect]
      ring
    _ = μ.expect (fun ω => ∑ a, g a * (bit (Z ω = a) * f ω)) := by
      simp only [← μ.expect_mul, ← μ.expect_sum]
    _ = _ := by
      apply μ.expect_congr
      intro ω
      simp [bit]

theorem given_pullout (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) (g : B → ℝ) (f : Ω → ℝ) :
    (μ.given Y b).expect (fun ω => g (Y ω) * f ω) = g b * (μ.given Y b).expect f := by
  apply mul_left_cancel₀ (ne_of_gt hb)
  rw [μ.weighted_given_expect]
  calc
    _ = g b * μ.expect (fun ω => bit (Y ω = b) * f ω) := by
      rw [← μ.expect_mul]
      apply μ.expect_congr
      intro ω
      by_cases h : Y ω = b <;> simp [bit, h, mul_assoc]
    _ = _ := by rw [← μ.weighted_given_expect]; ring

/-- Exact tower identity for nested views. The coarse view is explicitly f ∘ Z. -/
theorem given_tower (μ : FiniteProb Ω) (Z : Ω → A) (coarse : A → B) (b : B)
    (hb : 0 < (μ.map (fun ω => coarse (Z ω))).weight b) (f : Ω → ℝ) :
    (μ.given (fun ω => coarse (Z ω)) b).expect
        (fun ω => (μ.given Z (Z ω)).expect f) =
      (μ.given (fun ω => coarse (Z ω)) b).expect f := by
  apply mul_left_cancel₀ (ne_of_gt hb)
  rw [μ.weighted_given_expect, μ.weighted_given_expect]
  exact μ.expect_mul_given Z (fun a => bit (coarse a = b)) f

/-- One full first-failure induction step: coarse measurable keeping commutes
with averaging an original-rule conditional probability from the larger view. -/
theorem filtered_tower (μ : FiniteProb Ω) (Z : Ω → A) (coarse : A → B) (b : B)
    (hb : 0 < (μ.map (fun ω => coarse (Z ω))).weight b)
    (keep : B → Prop) (f : Ω → ℝ) :
    (μ.given (fun ω => coarse (Z ω)) b).expect
        (fun ω => bit (keep (coarse (Z ω))) * (μ.given Z (Z ω)).expect f) =
      bit (keep b) * (μ.given (fun ω => coarse (Z ω)) b).expect f := by
  rw [μ.given_pullout _ b hb (fun b => bit (keep b)), μ.given_tower Z coarse b hb f]

/-- The occupied mass can be split using ANY finite classification of outputs.
Taking the classification to be first failure or final survival yields exactly
the entropy partition needed by the occupancy proof; no independence is used. -/
theorem classified_mass_sum (μ : FiniteProb Ω) {I : Type*} [Fintype I]
    (occupied : Ω → Prop) (classify : Ω → I) :
    (∑ i, μ.prob (fun ω => occupied ω ∧ classify ω = i)) = μ.prob occupied := by
  unfold prob
  rw [← μ.expect_sum]
  apply μ.expect_congr
  intro ω
  by_cases h : occupied ω <;> simp [bit, h]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/ProjectedBudget.lean ===== -/

/-!
# Joint conflict budget for classified parts of an actual zero-conflict output

The parts need not be independent. Their occupied masses sum to the original
occupied mass, each part inherits zero conflict, and direct projection charges
their entropies jointly. The remaining tree-entropy and support-list hypotheses
are spelled out for every part.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def selectedConflict {C A B : Type*} (E : C → A → B → Prop)
    (t : C × Option A × Option B) : Prop :=
  match t.2.1, t.2.2 with
  | some a, some b => E t.1 a b
  | _, _ => False

def classifiedOutput {Ω I A : Type*} (U : Ω → Option A) (classify : Ω → I) (i : I) :
    Ω → Option A := fun ω => if classify ω = i then U ω else none

theorem classified_conflict_subset {Ω I A B C : Type*}
    (U : Ω → Option A) (V : Ω → Option B) (cu cv : Ω → I) (i : I)
    (F : Ω → C) (E : C → A → B → Prop) (ω : Ω) :
    selectedConflict E (F ω, classifiedOutput U cu i ω, classifiedOutput V cv i ω) →
      selectedConflict E (F ω,U ω,V ω) := by
  by_cases hu : cu ω = i <;> by_cases hv : cv ω = i
  · simp [classifiedOutput, hu, hv]
  · cases hU : U ω <;> simp [classifiedOutput, hu, hv, selectedConflict, hU]
  · simp [classifiedOutput, hu, hv, selectedConflict]
  · simp [classifiedOutput, hu, hv, selectedConflict]

namespace FiniteProb

variable {Ω I A B C Y Z : Type*}
  [Fintype Ω] [Fintype I] [Fintype A] [Fintype B] [Fintype C] [Fintype Y] [Fintype Z]

omit [Fintype A] in
theorem classified_occupancy_sum (μ : FiniteProb Ω)
    (U : Ω → Option A) (c : Ω → I) :
    (∑ i, μ.prob (fun ω => classifiedOutput U c i ω ≠ none)) =
      μ.prob (fun ω => U ω ≠ none) := by
  convert μ.classified_mass_sum (fun ω => U ω ≠ none) c using 1
  apply Finset.sum_congr rfl
  intro i _
  apply μ.prob_congr
  intro ω
  by_cases h : c ω = i <;> simp [classifiedOutput, h]

omit [Fintype I] in
theorem classified_zero_conflict (μ : FiniteProb Ω)
    (U : Ω → Option A) (V : Ω → Option B) (cu cv : Ω → I) (i : I)
    (F : Ω → C) (E : C → A → B → Prop)
    (hz : μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) = 0) :
    (μ.map (fun ω => (F ω,classifiedOutput U cu i ω,classifiedOutput V cv i ω))).prob
      (selectedConflict E) = 0 := by
  rw [μ.prob_map]
  apply le_antisymm _ (μ.prob_nonneg _)
  calc
    _ ≤ μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) :=
      μ.prob_mono (classified_conflict_subset U V cu cv i F E)
    _ = 0 := hz

/-- The manuscript's joint first-failure budget, at the finite-distribution level.
The part index has cardinality r. A concrete rule must still supply its smaller
views, short lists, symmetry, and the tree entropy inequality. -/
theorem classified_projected_budget [Nonempty I] (μ : FiniteProb Ω)
    (U : Ω → Option A) (V : Ω → Option B) (cu cv : Ω → I)
    (F : I → Ω → C) (y : I → C → Y) (z : I → C → Z)
    (S : I → Y → Finset A) (E : C → A → B → Prop) {D m p : ℝ}
    (hD : 0 < D) (hm : 1 ≤ m) (hp : p ≤ 1)
    (hmass : μ.prob (fun ω => U ω ≠ none) ≤ p)
    (hzero : ∀ i, μ.prob (fun ω => selectedConflict E (F i ω,U ω,V ω)) = 0)
    (hcard : ∀ i b, ((S i b).card : ℝ) ≤ m)
    (hsupport : ∀ i b, 0 < (μ.map (fun ω => y i (F i ω))).weight b →
      ∀ a, a ∉ S i b →
        ((μ.given (fun ω => y i (F i ω)) b).map (classifiedOutput U cu i)).weight (some a) = 0)
    (hsym : ∀ i, μ.condEntropy (classifiedOutput V cv i) (fun ω => z i (F i ω)) =
      μ.condEntropy (classifiedOutput U cu i) (fun ω => y i (F i ω)))
    (htree : ∀ i, (D-1) * μ.condEntropy (classifiedOutput U cu i) (fun ω => y i (F i ω)) ≤
      D/2 * μ.condEntropy (fun ω => (classifiedOutput U cu i ω,classifiedOutput V cv i ω)) (F i)) :
    (∑ i, (μ.projectedPair (F i) (classifiedOutput U cu i) (classifiedOutput V cv i)
      (y i) (z i)).prob (selectedConflict E)) ≤ 2 * massBudget (m * Fintype.card I) p / D := by
  apply joint_conflict_budget
    (fun i => μ.prob (fun ω => classifiedOutput U cu i ω ≠ none)) _
    hD hm (fun i => μ.prob_nonneg _) hp
  · rw [μ.classified_occupancy_sum]
    exact hmass
  · intro i
    exact μ.direct_projection_rare_bound (F i) (classifiedOutput U cu i)
      (classifiedOutput V cv i) (y i) (z i) (S i) (selectedConflict E)
      hD (lt_of_lt_of_le zero_lt_one hm) (le_refl 0) (hcard i) (hsupport i)
      (hsym i) (by simpa using htree i) (μ.classified_zero_conflict U V cu cv i (F i) E (hzero i))

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/OccupancyNumerics.lean ===== -/

/-!
# Occupancy accounting and the constant 5000

These results close the numerical argument from explicitly stated mass-loss
and conflict-budget estimates. They do not assert that a concrete tree rule
satisfies the list-truncation estimate or the tree entropy inequality.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

/-- Cauchy--Schwarz combines all deleted parts and the final zero-radius rule.
All differences are real differences, even when p is below r*b. -/
theorem occupancy_excess_squared {I : Type*} [Fintype I]
    (τ w : I → ℝ) {p pf ε b : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hε : 0 ≤ ε) (hpf : 0 ≤ pf)
    (hfinal : pf^2 = 2*ε) (hmass : p = pf + ∑ i, τ i)
    (hloss : ∀ i, τ i ≤ b + 6*Real.sqrt (w i))
    (hexcess : (Fintype.card I : ℝ)*b ≤ p) :
    (p - (Fintype.card I : ℝ)*b)^2 ≤
      (36*(Fintype.card I : ℝ)+2) * (ε + ∑ i, w i) := by
  have hpf' : pf = Real.sqrt 2 * Real.sqrt ε := by
    have hs : (Real.sqrt 2 * Real.sqrt ε)^2 = 2*ε := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt hε]
    have hn := mul_nonneg (Real.sqrt_nonneg (2:ℝ)) (Real.sqrt_nonneg ε)
    nlinarith
  let a : Option I → ℝ := fun i => match i with | none => Real.sqrt 2 | some _ => 6
  let c : Option I → ℝ := fun i => match i with | none => Real.sqrt ε | some i => Real.sqrt (w i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) a c
  simp only [Fintype.sum_option, a, c, Real.sq_sqrt hε, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.sq_sqrt (hw _), Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcs
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hloss i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hp : p - (Fintype.card I : ℝ)*b ≤
      Real.sqrt 2 * Real.sqrt ε + ∑ i, 6*Real.sqrt (w i) := by rw [← hpf']; linarith
  have hnq : 0 ≤ Real.sqrt 2 * Real.sqrt ε + ∑ i, 6*Real.sqrt (w i) := by positivity
  have hq := sq_le_sq₀ (sub_nonneg.mpr hexcess) hnq
  have hs := (hq.mpr hp).trans hcs
  nlinarith

/-- The logarithmic simplification in the nontrivial parameter regime. -/
theorem massBudget_le_seven {D m r p : ℝ}
    (hD : 0 < D) (hlog : 1 ≤ Real.log D) (hm : 0 < m)
    (hmupper : m ≤ D^4) (hr : 0 < r) (hrupper : r ≤ D) (hp : 1/D ≤ p) :
    massBudget (m*r) p ≤ 7*p*Real.log D := by
  have hp' : 0 < p := lt_of_lt_of_le (one_div_pos.mpr hD) hp
  have hml := Real.log_le_log hm hmupper
  rw [Real.log_pow] at hml
  have hrl := Real.log_le_log hr hrupper
  have hpl := Real.log_le_log (one_div_pos.mpr hD) hp
  simp only [one_div, Real.log_inv] at hpl
  have heq : massBudget (m*r) p = p * (1 + Real.log m + Real.log r - Real.log p) := by
    rw [massBudget, Real.log_mul (ne_of_gt hm) (ne_of_gt hr), Real.negMulLog]
    ring
  rw [heq]
  have hinside : 1 + Real.log m + Real.log r - Real.log p ≤ 7*Real.log D := by
    norm_num at hml
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hinside hp'.le]

/-- Solves the necessary occupancy inequality, including r>D and p<1/D.
No desired occupancy conclusion is built into an algorithm definition. -/
theorem occupancy_cap_from_squared_budget {r : ℕ} {D m p S : ℝ}
    (hr : 1 ≤ r) (hD : 0 < D) (hlog : 1 ≤ Real.log D)
    (hm : 0 < m) (hmupper : m ≤ D^4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbudget : S ≤ 2 * massBudget (m*(r:ℝ)) p / D)
    (hexcess : (r:ℝ)*(2100*Real.log D/D) ≤ p →
      (p - (r:ℝ)*(2100*Real.log D/D))^2 ≤ (36*(r:ℝ)+2)*S) :
    p ≤ occupancyCap r D := by
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0:ℝ) < r := lt_of_lt_of_le zero_lt_one hr1
  have hl0 : 0 ≤ Real.log D := le_trans (by norm_num) hlog
  let t : ℝ := (r:ℝ)*Real.log D/D
  have ht0 : 0 ≤ t := div_nonneg (mul_nonneg hr0.le hl0) hD.le
  have ht_eq : (r:ℝ)*(2100*Real.log D/D) = 2100*t := by dsimp [t]; ring
  have hbound : p ≤ 5000*t := by
    by_cases hrD : (r:ℝ) ≤ D
    · by_cases hpD : 1/D ≤ p
      · have hs := hbudget.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (massBudget_le_seven hD hlog hm hmupper hr0 hrD hpD)
            (by norm_num)) hD.le)
        by_cases he : (r:ℝ)*(2100*Real.log D/D) ≤ p
        · have hq := (hexcess he).trans (mul_le_mul_of_nonneg_left hs (by positivity))
          have hc : (36*(r:ℝ)+2) * (2*(7*p*Real.log D)/D) ≤ 532*t*p := by
            have hcoef : 14*(36*(r:ℝ)+2) ≤ 532*(r:ℝ) := by linarith
            have hv : 0 ≤ p*Real.log D/D := div_nonneg (mul_nonneg hp0 hl0) hD.le
            have hh := mul_le_mul_of_nonneg_right hcoef hv
            dsimp [t]
            convert hh using 1 <;> ring
          have hq' := hq.trans hc
          rw [ht_eq] at hq'
          have h4732 : p ≤ 4732*t := by
            by_contra h
            have hpos : 0 < p := lt_of_le_of_lt (by positivity : (0:ℝ) ≤ 4732*t) (lt_of_not_ge h)
            have hprod := mul_pos hpos (sub_pos.mpr (lt_of_not_ge h))
            nlinarith [sq_nonneg (2100*t)]
          linarith
        · rw [ht_eq] at he
          linarith [le_of_not_ge he]
      · have hc : 1/D ≤ 5000*t := by
          apply (div_le_iff₀ hD).mpr
          have hmul : 1 ≤ (r:ℝ)*Real.log D := one_le_mul_of_one_le_of_one_le hr1 hlog
          dsimp [t]
          rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hD)]
          nlinarith
        exact (le_of_not_ge hpD).trans hc
    · have hrt : 1 ≤ t := by
        apply (le_div_iff₀ hD).mpr
        have hmul := mul_le_mul_of_nonneg_left hlog hr0.le
        simp only [mul_one, one_mul] at hmul ⊢
        exact (le_of_not_ge hrD).trans hmul
      linarith
  apply le_min hp1
  change p ≤ 5000*(r:ℝ)*Real.log D/D
  convert hbound using 1
  dsimp [t]
  ring

/-- Full scalar endgame, retaining the two unresolved mathematical estimates
(truncation loss and the joint conflict budget) as explicit hypotheses. -/
theorem occupancy_from_reduction_estimates {r : ℕ} {D m p pf ε : ℝ}
    (τ w : Fin r → ℝ) (hr : 1 ≤ r) (hD : 0 < D) (hlog : 1 ≤ Real.log D)
    (hm : 0 < m) (hmupper : m ≤ D^4) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hw : ∀ i, 0 ≤ w i) (hε : 0 ≤ ε) (hpf : 0 ≤ pf)
    (hfinal : pf^2 = 2*ε) (hmass : p = pf + ∑ i, τ i)
    (hloss : ∀ i, τ i ≤ 2100*Real.log D/D + 6*Real.sqrt (w i))
    (hbudget : ε + ∑ i, w i ≤ 2 * massBudget (m*(r:ℝ)) p / D) :
    p ≤ occupancyCap r D := by
  apply occupancy_cap_from_squared_budget hr hD hlog hm hmupper hp0 hp1 hbudget
  intro he
  simpa only [Fintype.card_fin] using
    occupancy_excess_squared τ w hw hε hpf hfinal hmass hloss (by simpa using he)

end
end MISLocal


/- ===== Source: MISLocal/Hellinger.lean ===== -/

/-! Square-root event comparison, also needed for positive-conflict truncation. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem hellinger_term_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 < p → 0 < q) :
    (Real.sqrt p - Real.sqrt q)^2 ≤ p*(Real.log p - Real.log q) - p + q := by
  have hg := gibbs_term (Real.sqrt_nonneg p) (Real.sqrt_nonneg q)
    (fun h => Real.sqrt_pos.mpr (hs (Real.sqrt_pos.mp h)))
  rw [Real.log_sqrt hp, Real.log_sqrt hq] at hg
  have hm := mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg p)
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt hp] at hm
  have hsp := Real.sq_sqrt hp
  have hsq := Real.sq_sqrt hq
  nlinarith

namespace FiniteProb

variable {Ω : Type*} [Fintype Ω]

theorem prob_eq_sum_filter (μ : FiniteProb Ω) (E : Ω → Prop) :
    μ.prob E = ∑ ω ∈ Finset.univ.filter E, μ.weight ω := by
  simp [prob, expect, bit, Finset.sum_filter]

def hellingerSq (P Q : FiniteProb Ω) : ℝ :=
  ∑ ω, (Real.sqrt (P.weight ω) - Real.sqrt (Q.weight ω))^2

theorem hellingerSq_le_kl (P Q : FiniteProb Ω) (h : P.Dominated Q) :
    P.hellingerSq Q ≤ P.kl Q := by
  have hs := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) =>
    hellinger_term_le (P.nonneg ω) (Q.nonneg ω) (h ω))
  simpa [hellingerSq, kl, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    P.total, Q.total] using hs

theorem sqrt_event_sq_le_hellingerSq (P Q : FiniteProb Ω) (E : Ω → Prop) :
    (Real.sqrt (P.prob E) - Real.sqrt (Q.prob E))^2 ≤ P.hellingerSq Q := by
  let s := Finset.univ.filter E
  have hp : P.prob E = ∑ ω ∈ s, P.weight ω := P.prob_eq_sum_filter E
  have hq : Q.prob E = ∑ ω ∈ s, Q.weight ω := Q.prob_eq_sum_filter E
  have hcs := Real.sum_sqrt_mul_sqrt_le s P.nonneg Q.nonneg
  rw [← hp, ← hq] at hcs
  have heq : (∑ ω ∈ s, (Real.sqrt (P.weight ω)-Real.sqrt (Q.weight ω))^2) =
      P.prob E + Q.prob E - 2*(∑ ω ∈ s, Real.sqrt (P.weight ω)*Real.sqrt (Q.weight ω)) := by
    simp only [sub_sq, Real.sq_sqrt (P.nonneg _), Real.sq_sqrt (Q.nonneg _),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum,
      ← hp, ← hq]
    ring
  have hsub : (∑ ω ∈ s, (Real.sqrt (P.weight ω)-Real.sqrt (Q.weight ω))^2) ≤
      P.hellingerSq Q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω _ _ => sq_nonneg _)
  rw [heq] at hsub
  nlinarith [Real.sq_sqrt (P.prob_nonneg E), Real.sq_sqrt (Q.prob_nonneg E)]

theorem sqrt_event_sq_le_kl (P Q : FiniteProb Ω) (h : P.Dominated Q) (E : Ω → Prop) :
    (Real.sqrt (P.prob E) - Real.sqrt (Q.prob E))^2 ≤ P.kl Q :=
  (P.sqrt_event_sq_le_hellingerSq Q E).trans (P.hellingerSq_le_kl Q h)

theorem sqrt_event_le (P Q : FiniteProb Ω) (h : P.Dominated Q) (E : Ω → Prop) :
    Real.sqrt (Q.prob E) ≤ Real.sqrt (P.prob E) + Real.sqrt (P.kl Q) := by
  have hs := P.sqrt_event_sq_le_kl Q h E
  have hk := Real.sq_sqrt (P.kl_nonneg Q h)
  nlinarith [Real.sqrt_nonneg (P.prob E), Real.sqrt_nonneg (Q.prob E),
    Real.sqrt_nonneg (P.kl Q)]

/-- The form used to control coincident neighboring selection probabilities. -/
theorem event_le_two_mul_add_kl (P Q : FiniteProb Ω) (h : P.Dominated Q) (E : Ω → Prop) :
    Q.prob E ≤ 2*P.prob E + 2*P.kl Q := by
  have hs := P.sqrt_event_sq_le_kl Q h E
  have hp := Real.sq_sqrt (P.prob_nonneg E)
  have hq := Real.sq_sqrt (Q.prob_nonneg E)
  nlinarith [sq_nonneg (2*Real.sqrt (P.prob E) - Real.sqrt (Q.prob E))]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/Locality.lean ===== -/

/-!
# Causality of synchronous local computation and legal ID completion

A protocol has unrestricted state/messages and can use its local input each
round. Fixed node/port information can be included in the transition functions.
No symmetry is asserted here; that remains a separate obligation when turning
a concrete LOCAL algorithm into the anonymous edge-input model.

The LOCAL input comprises both an identifier and the tape stored at that
identifier. Thus the completion theorem preserves tapes as well as identifiers.
-/

namespace MISLocal
noncomputable section

def InBall {V : Type*} (G : SimpleGraph V) : ℕ → V → V → Prop
  | 0, v, u => u = v
  | t+1, v, u => u = v ∨ ∃ w, G.Adj v w ∧ InBall G t w u

theorem inBall_self {V : Type*} (G : SimpleGraph V) (t : ℕ) (v : V) : InBall G t v v := by
  cases t <;> simp [InBall]

theorem inBall_mono_succ {V : Type*} (G : SimpleGraph V) (t : ℕ) (v u : V) :
    InBall G t v u → InBall G (t+1) v u := by
  induction t generalizing v u with
  | zero => intro h; exact Or.inl h
  | succ t ih =>
    rintro (h | ⟨w, hvw, hwu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨w, hvw, ih w u hwu⟩

structure LocalProtocol {V : Type*} (G : SimpleGraph V) (Input State : Type*) where
  init : V → Input → State
  step : (t : ℕ) → (v : V) → Input → State → (G.neighborSet v → State) → State

namespace LocalProtocol

variable {V Input State : Type*} {G : SimpleGraph V}

def run (A : LocalProtocol G Input State) (input : V → Input) : ℕ → V → State
  | 0, v => A.init v (input v)
  | t+1, v => A.step t v (input v) (A.run input t v)
      (fun w => A.run input t w.val)

/-- One communication round expands the input-dependence ball by exactly one. -/
theorem run_local (A : LocalProtocol G Input State) (t : ℕ) (v : V)
    (x y : V → Input) (h : ∀ u, InBall G t v u → x u = y u) :
    A.run x t v = A.run y t v := by
  induction t generalizing v with
  | zero => simp only [run, h v (inBall_self G 0 v)]
  | succ t ih =>
    have hv := h v (inBall_self G (t+1) v)
    have hself := ih v (fun u hu => h u (inBall_mono_succ G t v u hu))
    have hn : (fun w : G.neighborSet v => A.run x t w.val) =
        (fun w : G.neighborSet v => A.run y t w.val) := by
      funext w
      apply ih w.val
      intro u hu
      exact h u (Or.inr ⟨w.val, w.property, hu⟩)
    simp only [run, hv, hself, hn]

def candidates (A : LocalProtocol G Input State) (out : V → State → Prop)
    (t : ℕ) (x : V → Input) : Set V := {v | out v (A.run x t v)}

/-- The conflict-removal postprocessing costs one more communication round. -/
theorem repair_local (A : LocalProtocol G Input State) (out : V → State → Prop)
    (t : ℕ) (v : V) (x y : V → Input)
    (h : ∀ u, InBall G (t+1) v u → x u = y u) :
    v ∈ repair G (A.candidates out t x) ↔ v ∈ repair G (A.candidates out t y) := by
  have hself := A.run_local t v x y (fun u hu => h u (inBall_mono_succ G t v u hu))
  have hn (w : V) (hw : G.Adj v w) : A.run x t w = A.run y t w :=
    A.run_local t w x y (fun u hu => h u (Or.inr ⟨w,hw,hu⟩))
  simp only [repair, Set.mem_setOf_eq, candidates, hself]
  constructor
  · rintro ⟨hv, hh⟩
    refine ⟨hv, fun w hw => ?_⟩
    simpa only [← hn w hw] using hh w hw
  · rintro ⟨hv, hh⟩
    refine ⟨hv, fun w hw => ?_⟩
    simpa only [hn w hw] using hh w hw

end LocalProtocol

/-- Local ID uniqueness is sufficient for the entire T-round simulation,
including ID-indexed tapes. Completion outside the ball is irrelevant. -/
theorem completed_ID_simulation {n : ℕ} {Tape State : Type*} (G : SimpleGraph (Fin n))
    (A : LocalProtocol G (Fin n × Tape) State) (t : ℕ) (v : Fin n)
    (ids : Fin n → Fin n) (W : Fin n → Tape)
    (hinj : Set.InjOn ids {u | InBall G t v u}) :
    A.run (fun u => (completeIDs {u | InBall G t v u} ids u,
        W (completeIDs {u | InBall G t v u} ids u))) t v =
      A.run (fun u => (ids u,W (ids u))) t v := by
  apply A.run_local
  intro u hu
  rw [completeIDs_agrees _ ids hinj u hu]

end
end MISLocal


/- ===== Source: MISLocal/ZeroRadius.lean ===== -/

/-!
# Exact zero-radius conflict probability

The two private outputs and the central matrix are sampled independently.
For independent fair matrix entries and identical output distributions this
proves epsilon = p^2/2 on the actual product probability space.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {M A B : Type*} [Fintype M] [Fintype A] [Fintype B]

def product (P : FiniteProb A) (Q : FiniteProb B) : FiniteProb (A × B) where
  weight ab := P.weight ab.1 * Q.weight ab.2
  nonneg ab := mul_nonneg (P.nonneg _) (Q.nonneg _)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, P.total, Q.total]

/-- Independence of the output draws from the matrix is imposed by the
product distribution, not asserted only through one-dimensional marginals. -/
theorem product_conflict_probability (μ : FiniteProb M)
    (P : FiniteProb (Option A)) (Q : FiniteProb (Option B))
    (E : M → A → B → Prop) {c : ℝ}
    (hfair : ∀ a b, μ.prob (fun g => E g a b) = c) :
    (μ.product (P.product Q)).prob (selectedConflict E) =
      P.prob (fun a => a ≠ none) * Q.prob (fun b => b ≠ none) * c := by
  have hswap : (μ.product (P.product Q)).prob (selectedConflict E) =
      P.expect (fun a => Q.expect (fun b => μ.prob (fun g => selectedConflict E (g,a,b)))) := by
    simp only [prob, expect, product, Fintype.sum_prod_type, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [hswap]
  have hnone (b : Option B) : μ.prob (fun g => selectedConflict E (g,none,b)) = 0 := by
    simp [selectedConflict]
  have hnone' (a : A) : μ.prob (fun g => selectedConflict E (g,some a,none)) = 0 := by
    simp [selectedConflict]
  simp only [expect, Fintype.sum_option, hnone, hnone', selectedConflict, hfair,
    prob_false, mul_zero, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ← Finset.sum_mul,
    P.occupied_mass, Q.occupied_mass]
  ring

end FiniteProb

/-- Every individual entry in a uniformly random Boolean matrix is fair. -/
theorem uniform_matrix_entry_fair {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : A) (b : B) :
    (FiniteProb.uniform (A × B → Bool)).prob (fun G => G (a,b) = true) = 1/2 := by
  have h := uniform_first_coordinate (Equiv.funSplitAt (a,b) Bool) true
  simpa using h

/-- A complete zero-radius instance with the actual independent edge matrix. -/
theorem zero_radius_conflict {A : Type*} [Fintype A] [DecidableEq A]
    (P : FiniteProb (Option A)) :
    ((FiniteProb.uniform (A × A → Bool)).product (P.product P)).prob
      (selectedConflict (fun G a b => G (a,b) = true)) =
        (P.prob (fun a => a ≠ none))^2 / 2 := by
  rw [FiniteProb.product_conflict_probability _ P P _ (fun a b => uniform_matrix_entry_fair a b)]
  ring

end
end MISLocal


/- ===== Source: MISLocal/TopLists.lean ===== -/

/-! Actual maximizing short lists and the pointwise bound outside them. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

variable {A : Type*} [Fintype A]

theorem exists_bestList (w : A → ℝ) (m : ℕ) :
    ∃ B : Finset A, B.card ≤ m ∧ ∀ S : Finset A, S.card ≤ m →
      (∑ a ∈ S, w a) ≤ ∑ a ∈ B, w a := by
  let choices := Finset.univ.powerset.filter (fun S : Finset A => S.card ≤ m)
  have he : (∅ : Finset A) ∈ choices := by simp [choices]
  obtain ⟨B, hB, hmax⟩ := choices.exists_max_image (fun S => ∑ a ∈ S, w a) ⟨∅,he⟩
  refine ⟨B, (Finset.mem_filter.mp hB).2, ?_⟩
  intro S hS
  exact hmax S (by simp [choices, hS])

def bestList (w : A → ℝ) (m : ℕ) : Finset A := (exists_bestList w m).choose

theorem bestList_card (w : A → ℝ) (m : ℕ) : (bestList w m).card ≤ m :=
  (exists_bestList w m).choose_spec.1

theorem bestList_optimal (w : A → ℝ) (m : ℕ) (S : Finset A) (hS : S.card ≤ m) :
    (∑ a ∈ S, w a) ≤ ∑ a ∈ bestList w m, w a :=
  (exists_bestList w m).choose_spec.2 S hS

theorem bestList_exchange (w : A → ℝ) (m : ℕ) {a b : A}
    (ha : a ∉ bestList w m) (hb : b ∈ bestList w m) : w a ≤ w b := by
  let B := bestList w m
  have hab : a ∉ B.erase b := fun h => ha (Finset.mem_erase.mp h).2
  have hc : (insert a (B.erase b)).card ≤ m := by
    rw [Finset.card_insert_of_not_mem hab, Finset.card_erase_of_mem hb]
    have hB := bestList_card w m
    have hpos := Finset.card_pos.mpr ⟨b,hb⟩
    dsimp [B] at *
    omega
  have h := bestList_optimal w m (insert a (B.erase b)) hc
  rw [Finset.sum_insert hab] at h
  have he := Finset.sum_erase_add B w hb
  change (∑ x ∈ B.erase b, w x) + w b = ∑ x ∈ bestList w m, w x at he
  linarith

theorem bestList_outside_zero_of_card_lt (w : A → ℝ) (m : ℕ)
    (hw : ∀ a, 0 ≤ w a) (hc : (bestList w m).card < m) {a : A}
    (ha : a ∉ bestList w m) : w a = 0 := by
  have hi : (insert a (bestList w m)).card ≤ m := by
    rw [Finset.card_insert_of_not_mem ha]
    omega
  have h := bestList_optimal w m _ hi
  rw [Finset.sum_insert ha] at h
  exact le_antisymm (by linarith) (hw a)

/-- Every omitted weight is at most total mass divided by the list capacity.
This includes the case where the capacity exceeds the entire alphabet. -/
theorem bestList_outside_le (w : A → ℝ) (m : ℕ) (hm : 0 < m)
    (hw : ∀ a, 0 ≤ w a) {a : A} (ha : a ∉ bestList w m) :
    w a ≤ (∑ b, w b) / (m : ℝ) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  by_cases hc : (bestList w m).card = m
  · have hs : (m:ℝ)*w a ≤ ∑ b ∈ bestList w m, w b := by
      calc
        _ = ∑ _b ∈ bestList w m, w a := by simp [hc]
        _ ≤ _ := Finset.sum_le_sum (fun b hb => bestList_exchange w m ha hb)
    have hall := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (bestList w m))
      (fun b _ _ => hw b)
    apply (le_div_iff₀ hm').mpr
    nlinarith [hs.trans hall]
  · have hc' : (bestList w m).card < m := lt_of_le_of_ne (bestList_card w m) hc
    rw [bestList_outside_zero_of_card_lt w m hw hc' ha]
    exact div_nonneg (Finset.sum_nonneg (fun b _ => hw b)) hm'.le

namespace FiniteProb

def outputList (μ : FiniteProb (Option A)) (m : ℕ) : Finset A :=
  bestList (fun a => μ.weight (some a)) m

def listTail (μ : FiniteProb (Option A)) (S : Finset A) : ℝ :=
  ∑ a ∈ Finset.univ \ S, μ.weight (some a)

def tail (μ : FiniteProb (Option A)) (m : ℕ) : ℝ := μ.listTail (μ.outputList m)

theorem listTail_eq (μ : FiniteProb (Option A)) (S : Finset A) :
    μ.listTail S = μ.prob (fun a => a ≠ none) - ∑ a ∈ S, μ.weight (some a) := by
  have h := Finset.sum_sdiff (f := fun a => μ.weight (some a)) (Finset.subset_univ S)
  rw [μ.occupied_mass] at h
  change μ.listTail S + (∑ a ∈ S, μ.weight (some a)) = _ at h
  linarith

theorem listTail_nonneg (μ : FiniteProb (Option A)) (S : Finset A) : 0 ≤ μ.listTail S :=
  Finset.sum_nonneg (fun a _ => μ.nonneg (some a))

theorem listTail_le_one (μ : FiniteProb (Option A)) (S : Finset A) : μ.listTail S ≤ 1 := by
  rw [μ.listTail_eq]
  have h := Finset.sum_nonneg (s := S) (fun a _ => μ.nonneg (some a))
  linarith [μ.prob_le_one (fun a => a ≠ none)]

theorem tail_minimal (μ : FiniteProb (Option A)) (m : ℕ) (S : Finset A) (hS : S.card ≤ m) :
    μ.tail m ≤ μ.listTail S := by
  unfold tail
  rw [μ.listTail_eq, μ.listTail_eq]
  have h := bestList_optimal (fun a => μ.weight (some a)) m S hS
  exact sub_le_sub_left h _

theorem outside_outputList_le (μ : FiniteProb (Option A)) (m : ℕ) (hm : 0 < m)
    {a : A} (ha : a ∉ μ.outputList m) : μ.weight (some a) ≤ 1/(m:ℝ) := by
  have h := bestList_outside_le (fun a => μ.weight (some a)) m hm (fun a => μ.nonneg _) ha
  rw [μ.occupied_mass] at h
  exact h.trans (div_le_div_of_nonneg_right (μ.prob_le_one _) (Nat.cast_nonneg _))

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/IndependentEvents.lean ===== -/

/-!
# Independent finite inputs and exponential estimates

Independence here means factorization of expectations of products. It is proved
for the actual product distribution, including dependent finite coordinate
types. Event independence is the corresponding identity for every subfamily.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

def pi {A : I → Type*} [DecidableEq I] [∀ i, Fintype (A i)]
    (P : ∀ i, FiniteProb (A i)) : FiniteProb (∀ i, A i) where
  weight x := ∏ i, (P i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp only [(P _).total, Finset.prod_const_one]

theorem expect_pi_prod {A : I → Type*} [DecidableEq I] [∀ i, Fintype (A i)]
    (P : ∀ i, FiniteProb (A i)) (f : ∀ i, A i → ℝ) :
    (pi P).expect (fun x => ∏ i, f i (x i)) = ∏ i, (P i).expect (f i) := by
  simp only [expect, pi, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).weight a * f i a)).symm

def Independent {A : I → Type*} (μ : FiniteProb Ω) (X : ∀ i, Ω → A i) : Prop :=
  ∀ f : ∀ i, A i → ℝ, μ.expect (fun ω => ∏ i, f i (X i ω)) =
    ∏ i, μ.expect (fun ω => f i (X i ω))

theorem pi_expect_coordinate {A : I → Type*} [DecidableEq I] [∀ i, Fintype (A i)]
    (P : ∀ i, FiniteProb (A i)) (i : I) (f : A i → ℝ) :
    (pi P).expect (fun x => f (x i)) = (P i).expect f := by
  classical
  let g : ∀ j, A j → ℝ := fun j => if h : j = i then fun a => f (h ▸ a) else fun _ => 1
  have hg (x : ∀ j, A j) : (∏ j, g j (x j)) = f (x i) := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro b _ hb
      simp [g, hb]
    · simp
  have he : (∏ j, (P j).expect (g j)) = (P i).expect f := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro b _ hb
      simp [g, hb]
    · simp
  rw [← he, ← expect_pi_prod P g]
  exact (pi P).expect_congr (fun x => (hg x).symm)

theorem pi_independent {A : I → Type*} [DecidableEq I] [∀ i, Fintype (A i)]
    (P : ∀ i, FiniteProb (A i)) : (pi P).Independent (fun i x => x i) := by
  intro f
  simp only [pi_expect_coordinate, expect_pi_prod]

theorem Independent.comp {A B : I → Type*} {μ : FiniteProb Ω}
    {X : ∀ i, Ω → A i} (h : μ.Independent X) (f : ∀ i, A i → B i) :
    μ.Independent (fun i ω => f i (X i ω)) := by
  intro g
  exact h (fun i a => g i (f i a))

def IndependentEvents (μ : FiniteProb Ω) (E : I → Ω → Prop) : Prop :=
  ∀ s : Finset I, μ.expect (fun ω => ∏ i ∈ s, bit (E i ω)) =
    ∏ i ∈ s, μ.prob (E i)

theorem Independent.events {A : I → Type*} {μ : FiniteProb Ω}
    {X : ∀ i, Ω → A i} (h : μ.Independent X) (E : ∀ i, A i → Prop) :
    μ.IndependentEvents (fun i ω => E i (X i ω)) := by
  intro s
  have hh := h (fun i a => if i ∈ s then bit (E i a) else 1)
  have hx (i : I) : μ.expect (fun ω => if i ∈ s then bit (E i (X i ω)) else 1) =
      if i ∈ s then μ.prob (fun ω => E i (X i ω)) else 1 := by
    by_cases hi : i ∈ s <;> simp [hi, prob]
  simpa only [hx, Finset.prod_ite_mem, Finset.inter_univ, Finset.univ_inter] using hh

theorem IndependentEvents.affine {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) (c : I → ℝ) :
    μ.expect (fun ω => ∏ i, (1 + c i * bit (E i ω))) =
      ∏ i, (1 + c i * μ.prob (E i)) := by
  simp only [Finset.prod_one_add]
  rw [μ.expect_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.prod_mul_distrib, μ.expect_mul, h s]

def eventCount (E : I → Ω → Prop) (ω : Ω) : ℝ := ∑ i, bit (E i ω)

def eventMean (μ : FiniteProb Ω) (E : I → Ω → Prop) : ℝ := ∑ i, μ.prob (E i)

theorem eventMean_nonneg (μ : FiniteProb Ω) (E : I → Ω → Prop) :
    0 ≤ μ.eventMean E := Finset.sum_nonneg (fun i _ => μ.prob_nonneg (E i))

theorem expect_eventCount (μ : FiniteProb Ω) (E : I → Ω → Prop) :
    μ.expect (eventCount E) = μ.eventMean E := μ.expect_sum _ _

theorem IndependentEvents.exp_expect {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) (t : ℝ) :
    μ.expect (fun ω => Real.exp (t * eventCount E ω)) =
      ∏ i, (1 + (Real.exp t - 1) * μ.prob (E i)) := by
  have he (ω : Ω) : Real.exp (t * eventCount E ω) =
      ∏ i, (1 + (Real.exp t - 1) * bit (E i ω)) := by
    simp only [eventCount, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : E i ω <;> simp [bit, hi]
  rw [μ.expect_congr he]
  exact h.affine _

theorem IndependentEvents.exp_expect_le {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) (t : ℝ) :
    μ.expect (fun ω => Real.exp (t * eventCount E ω)) ≤
      Real.exp ((Real.exp t - 1) * μ.eventMean E) := by
  rw [h.exp_expect]
  calc
    _ ≤ ∏ i, Real.exp ((Real.exp t - 1) * μ.prob (E i)) := by
      apply Finset.prod_le_prod
      · intro i _
        have hp := μ.prob_nonneg (E i)
        have hp' := μ.prob_le_one (E i)
        nlinarith [mul_nonneg (Real.exp_pos t).le hp]
      · intro i _
        linarith [Real.add_one_le_exp ((Real.exp t - 1) * μ.prob (E i))]
    _ = _ := by rw [← Real.exp_sum]; simp [eventMean, Finset.mul_sum]

/-- Markov's inequality with a strictly positive real threshold. -/
theorem prob_ge_le_expect_div (μ : FiniteProb Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {a : ℝ} (ha : 0 < a) :
    μ.prob (fun ω => a ≤ f ω) ≤ μ.expect f / a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm, prob, ← μ.expect_mul]
  exact μ.expect_mono (fun ω => by
    by_cases h : a ≤ f ω <;> simp [bit, h, hf ω, h])

/-- A lower-tail Chernoff bound, with the explicit constant used in the
short-list consolidation argument. No independence of outputs is needed. -/
theorem IndependentEvents.lower_tail {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) :
    μ.prob (fun ω => eventCount E ω < 7 * μ.eventMean E / 8) ≤
      Real.exp (-μ.eventMean E / 128) := by
  have hnum : Real.exp (-(1:ℝ)/8) ≤ 113/128 := by
    have hq := Real.quadratic_le_exp_of_nonneg (x := (1:ℝ)/8) (by norm_num)
    have hp := Real.exp_pos ((1:ℝ)/8)
    rw [show -(1:ℝ)/8 = -((1:ℝ)/8) by ring, Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hmono : μ.prob (fun ω => eventCount E ω < 7 * μ.eventMean E / 8) ≤
      μ.prob (fun ω => Real.exp (-(7 * μ.eventMean E / 8)/8) ≤
        Real.exp (-eventCount E ω/8)) := by
    apply μ.prob_mono
    intro ω hω
    exact Real.exp_le_exp.mpr (by linarith)
  have hm := μ.prob_ge_le_expect_div (fun ω => Real.exp (-eventCount E ω/8))
    (fun ω => (Real.exp_pos _).le) (Real.exp_pos (-(7 * μ.eventMean E / 8)/8))
  have he := h.exp_expect_le (-(1:ℝ)/8)
  have he' : μ.expect (fun ω => Real.exp (-eventCount E ω/8)) ≤
      Real.exp ((Real.exp (-(1:ℝ)/8)-1)*μ.eventMean E) := by
    convert he using 1
    congr 1
    funext ω
    congr 1
    ring
  calc
    _ ≤ _ := hmono.trans hm
    _ ≤ Real.exp ((Real.exp (-(1:ℝ)/8)-1)*μ.eventMean E) /
        Real.exp (-(7*μ.eventMean E/8)/8) :=
      div_le_div_of_nonneg_right he' (Real.exp_pos _).le
    _ = Real.exp (((Real.exp (-(1:ℝ)/8)-1)+7/64)*μ.eventMean E) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hn := μ.eventMean_nonneg E
      nlinarith)

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/DenseMatrix.lean ===== -/

/-!
# Dense rectangles force conflict between diffuse output distributions

The proof uses two weighted averaging arguments. It needs no sequential
sampling, no division by a possibly zero tail, and no independence assumption
other than the product of the two output weights in the stated conclusion.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {A B : Type*} [Fintype A] [Fintype B]

/-- If every list of `ell` values has average at least `c`, then weighting the
values by a subprobability distribution costs at most its best `ell` atoms.
The alphabet may be smaller than `ell`; in that case the tail is zero. -/
theorem weighted_tail_lower (P : FiniteProb (Option A)) (v : A → ℝ)
    (hv : ∀ a, 0 ≤ v a) {ell : ℕ} (hell : 0 < ell) {c : ℝ} (hc : 0 ≤ c)
    (hsets : ∀ S : Finset A, S.card = ell → (ell : ℝ) * c ≤ ∑ a ∈ S, v a) :
    P.tail ell * c ≤ ∑ a, P.weight (some a) * v a := by
  let bad : Finset A := Finset.univ.filter (fun a => v a < c)
  have hbad : bad.card < ell := by
    by_contra h
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun a ha =>
      (Finset.mem_filter.mp (hS ha)).2)
    have hs := hsets S hcard
    simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hlt
    exact not_lt_of_ge hs hlt
  have hgood {a : A} (ha : a ∈ Finset.univ \ bad) : c ≤ v a := by
    have hn := (Finset.mem_sdiff.mp ha).2
    simpa [bad, not_lt] using hn
  calc
    _ ≤ P.listTail bad * c := mul_le_mul_of_nonneg_right (P.tail_minimal ell bad hbad.le) hc
    _ = ∑ a ∈ Finset.univ \ bad, P.weight (some a) * c := by
      simp only [listTail, Finset.sum_mul]
    _ ≤ ∑ a ∈ Finset.univ \ bad, P.weight (some a) * v a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (hgood ha) (P.nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun a _ _ => mul_nonneg (P.nonneg _) (hv a))

/-- A matrix with every `ell`-by-`ell` rectangle of density at least `rho`
has weighted density at least `rho` times the product of the two tails. -/
theorem dense_rectangle_tail_product (P : FiniteProb (Option A))
    (Q : FiniteProb (Option B)) (G : A → B → ℝ)
    (hG : ∀ a b, 0 ≤ G a b) {ell : ℕ} (hell : 0 < ell)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hdense : ∀ S : Finset A, S.card = ell → ∀ T : Finset B, T.card = ell →
      rho * (ell : ℝ)^2 ≤ ∑ a ∈ S, ∑ b ∈ T, G a b) :
    rho * P.tail ell * Q.tail ell ≤
      ∑ a, ∑ b, P.weight (some a) * Q.weight (some b) * G a b := by
  have ht := Q.listTail_nonneg (Q.outputList ell)
  change 0 ≤ Q.tail ell at ht
  have h := P.weighted_tail_lower (fun a => ∑ b, Q.weight (some b) * G a b)
    (fun a => Finset.sum_nonneg (fun b _ => mul_nonneg (Q.nonneg _) (hG a b)))
    hell (c := rho * Q.tail ell) (mul_nonneg hrho ht) (by
      intro S hS
      have hinner := Q.weighted_tail_lower (fun b => ∑ a ∈ S, G a b)
        (fun b => Finset.sum_nonneg (fun a _ => hG a b)) hell
        (c := rho * ell) (mul_nonneg hrho (Nat.cast_nonneg _)) (by
          intro T hT
          have hrect := hdense S hS T hT
          rw [Finset.sum_comm] at hrect
          nlinarith)
      simp only [Finset.mul_sum] at hinner
      rw [Finset.sum_comm] at hinner
      nlinarith)
  simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

/-- The form used for Boolean conflict matrices. Zero tails are handled
directly, without cancellation or a hidden positivity premise. -/
theorem dense_boolean_tail_product (P : FiniteProb (Option A))
    (Q : FiniteProb (Option B)) (G : A → B → Prop)
    {ell : ℕ} (hell : 0 < ell)
    (hdense : ∀ S : Finset A, S.card = ell → ∀ T : Finset B, T.card = ell →
      (ell : ℝ)^2 / 4 ≤ ∑ a ∈ S, ∑ b ∈ T, bit (G a b)) :
    P.tail ell * Q.tail ell ≤
      4 * ∑ a, ∑ b, P.weight (some a) * Q.weight (some b) * bit (G a b) := by
  have h := P.dense_rectangle_tail_product Q (fun a b => bit (G a b))
    (fun a b => bit_nonneg _) hell (rho := 1/4) (by norm_num)
    (by intro S hS T hT; convert hdense S hS T hT using 1; ring)
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/FrequentLabels.lean ===== -/

/-!
# Consolidating independent short lists

The exponential estimate keeps a factor of the mean. Consequently a union
bound over labels depends on the sum of their weights, not alphabet size.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  rw [he] at h
  nlinarith

namespace FiniteProb

variable {Ω I A : Type*} [Fintype Ω] [Fintype I] [Fintype A]

/-- An upper tail with an essential mean prefactor. -/
theorem IndependentEvents.upper_tail_with_mean {μ : FiniteProb Ω}
    {E : I → Ω → Prop} (h : μ.IndependentEvents E) {a : ℝ} (ha : 1 ≤ a) :
    μ.prob (fun ω => a ≤ eventCount E ω) ≤
      4 * μ.eventMean E * Real.exp (2 * μ.eventMean E - a) := by
  have he1 : Real.exp 1 - 1 ≤ (2:ℝ) := by
    have he := Real.abs_exp_sub_one_le (x := (1:ℝ)) (by norm_num)
    exact (le_abs_self _).trans (by simpa using he)
  have hmean := μ.eventMean_nonneg E
  have he := (h.exp_expect_le 1).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right he1 hmean))
  simp only [one_mul] at he
  have h2 : (2:ℝ) ≤ Real.exp a := by
    have h1 := Real.add_one_le_exp (1:ℝ)
    have hm := Real.exp_le_exp.mpr ha
    linarith
  have hp : (Real.exp a / 2) * μ.prob (fun ω => a ≤ eventCount E ω) ≤
      μ.expect (fun ω => Real.exp (eventCount E ω) - 1) := by
    rw [prob, ← μ.expect_mul]
    apply μ.expect_mono
    intro ω
    have hn : 0 ≤ eventCount E ω := Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω))
    by_cases hω : a ≤ eventCount E ω
    · simp only [bit, if_pos hω, mul_one]
      have hm := Real.exp_le_exp.mpr hω
      linarith
    · simp only [bit, if_neg hω, mul_zero]
      have hm := Real.exp_le_exp.mpr hn
      simpa using sub_nonneg.mpr hm
  rw [μ.expect_sub, μ.expect_const] at hp
  have hp' : μ.prob (fun ω => a ≤ eventCount E ω) ≤
      4 * μ.eventMean E * Real.exp (2 * μ.eventMean E) / Real.exp a := by
    apply (le_div_iff₀ (Real.exp_pos a)).mpr
    nlinarith [exp_sub_one_le_mul_exp (2 * μ.eventMean E)]
  simpa only [Real.exp_sub, mul_div_assoc] using hp'

def labelWeight (μ : FiniteProb Ω) (L : I → Ω → Finset A) (a : A) : ℝ :=
  μ.eventMean (fun i ω => a ∈ L i ω)

def totalListWeight (μ : FiniteProb Ω) (L : I → Ω → Finset A) : ℝ :=
  ∑ a, μ.labelWeight L a

theorem totalListWeight_eq (μ : FiniteProb Ω) (L : I → Ω → Finset A) :
    μ.totalListWeight L = ∑ i, μ.expect (fun ω => ((L i ω).card : ℝ)) := by
  unfold totalListWeight labelWeight eventMean prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← μ.expect_sum]
  apply μ.expect_congr
  intro ω
  classical
  have hs := Finset.sum_subset (f := fun x => bit (x ∈ L i ω))
    (Finset.subset_univ (L i ω)) (fun x _ hx => by simp [bit, hx])
  rw [← hs]
  calc
    _ = ∑ _x ∈ L i ω, (1:ℝ) :=
      Finset.sum_congr rfl (fun x hx => by simp [bit, hx])
    _ = _ := by simp

/-- At most `M` fixed labels contain all labels that occur in many independent
lists, except with the stated probability. The lists need not be identically
distributed, and the sampled output may depend on every list. -/
theorem frequent_label_bound (μ : FiniteProb Ω) (L : I → Ω → Finset A)
    (hind : μ.Independent L) {M : ℕ} (hM : 0 < M) {a : ℝ} (ha : 1 ≤ a) :
    μ.prob (fun ω => ∃ b, b ∉ bestList (μ.labelWeight L) M ∧
      a ≤ eventCount (fun i ω => b ∈ L i ω) ω) ≤
      4 * μ.totalListWeight L * Real.exp (2 * μ.totalListWeight L / M - a) := by
  let C := μ.totalListWeight L
  let B := bestList (μ.labelWeight L) M
  have hw (b : A) : 0 ≤ μ.labelWeight L b := μ.eventMean_nonneg _
  have hout (b : A) (hb : b ∉ B) : μ.labelWeight L b ≤ C / M :=
    bestList_outside_le _ M hM hw hb
  have hbnd (b : A) : μ.prob (fun ω => b ∉ B ∧
      a ≤ eventCount (fun i ω => b ∈ L i ω) ω) ≤
      4 * μ.labelWeight L b * Real.exp (2*C/M-a) := by
    by_cases hb : b ∈ B
    · simp only [hb, not_true_eq_false, false_and, prob_false]
      exact mul_nonneg (mul_nonneg (by norm_num) (hw b)) (Real.exp_pos _).le
    · simp only [hb, not_false_eq_true, true_and]
      have he := (hind.events (fun _ S => b ∈ S)).upper_tail_with_mean ha
      apply he.trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (hw b))
      apply Real.exp_le_exp.mpr
      have hh := hout b hb
      change μ.eventMean (fun i ω => b ∈ L i ω) ≤ C / M at hh
      nlinarith only [hh, show 2*C/(M:ℝ) = 2*(C/M) by ring]
  calc
    _ ≤ ∑ b, μ.prob (fun ω => b ∉ B ∧ a ≤ eventCount (fun i ω => b ∈ L i ω) ω) :=
      μ.prob_exists_le_sum _
    _ ≤ ∑ b, 4 * μ.labelWeight L b * Real.exp (2*C/M-a) :=
      Finset.sum_le_sum (fun b _ => hbnd b)
    _ = _ := by simp [totalListWeight, C, ← Finset.sum_mul, ← Finset.mul_sum]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/ListCapture.lean ===== -/

/-! Captures may be arbitrarily dependent; only eligibility is independent. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω I A B : Type*} [Fintype Ω] [Fintype I] [Fintype A] [Fintype B]

theorem prob_indexed_conditioning (μ : FiniteProb Ω) (X : Ω → B)
    (E : B → Ω → Prop) :
    (∑ b, (μ.map X).weight b * (μ.given X b).prob (E b)) =
      μ.prob (fun ω => E (X ω) ω) := by
  simp only [prob, μ.weighted_given_expect]
  rw [← μ.expect_sum]
  apply μ.expect_congr
  intro ω
  rw [Finset.sum_eq_single (X ω)]
  · simp [bit]
  · intro b _ hb
    simp [bit, Ne.symm hb]
  · simp

theorem listTail_prob (P : FiniteProb (Option A)) (S : Finset A) :
    P.listTail S = P.prob (fun x => ∃ a, x = some a ∧ a ∉ S) := by
  simp only [listTail, prob, expect, Fintype.sum_option]
  rw [show bit (∃ a, (none : Option A) = some a ∧ a ∉ S) = 0 by simp [bit], mul_zero, zero_add]
  have he (b : A) : bit (∃ a, some b = some a ∧ a ∉ S) = bit (b ∉ S) := by
    congr 1
    simp
  simp only [he]
  calc
    _ = ∑ a ∈ Finset.univ \ S, P.weight (some a) * bit (a ∉ S) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [bit, (Finset.mem_sdiff.mp ha).2]
    _ = _ := Finset.sum_subset Finset.sdiff_subset (fun a _ ha => by
      have hm : a ∈ S := by simpa using ha
      simp [bit, hm])

omit [Fintype Ω] in
theorem eventCount_partition (E C : I → Ω → Prop) (ω : Ω) :
    eventCount E ω = eventCount (fun i ω => E i ω ∧ C i ω) ω +
      eventCount (fun i ω => E i ω ∧ ¬ C i ω) ω := by
  rw [eventCount, eventCount, eventCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hE : E i ω <;> by_cases hC : C i ω <;> simp [bit, hE, hC]

/-- This statement deliberately assumes no independence of `C`. -/
theorem many_eligible_captures (μ : FiniteProb Ω) (E C : I → Ω → Prop)
    (hind : μ.IndependentEvents E) {t : ℝ}
    (hmiss : ∀ i, μ.prob (fun ω => E i ω ∧ ¬ C i ω) ≤ t/2 * μ.prob (E i))
    (hsmall : Real.exp (-μ.eventMean E / 128) ≤ t/12)
    (hmean : 0 < μ.eventMean E) :
    μ.prob (fun ω => eventCount (fun i ω => E i ω ∧ C i ω) ω < μ.eventMean E/8) ≤
      3*t/4 := by
  let U := eventCount (fun i ω => E i ω ∧ ¬ C i ω)
  have hEU : μ.expect U ≤ t/2 * μ.eventMean E := by
    rw [show μ.expect U = ∑ i, μ.prob (fun ω => E i ω ∧ ¬ C i ω) from μ.expect_eventCount _]
    calc
      _ ≤ ∑ i, t/2 * μ.prob (E i) := Finset.sum_le_sum (fun i _ => hmiss i)
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hbad := μ.prob_mono (p := fun ω =>
    eventCount (fun i ω => E i ω ∧ C i ω) ω < μ.eventMean E/8)
    (q := fun ω => eventCount E ω < 7*μ.eventMean E/8 ∨ 3*μ.eventMean E/4 ≤ U ω) (by
      intro ω hω
      by_cases hL : eventCount E ω < 7*μ.eventMean E/8
      · exact Or.inl hL
      · right
        have heq := eventCount_partition E C ω
        change eventCount E ω = _ + U ω at heq
        linarith)
  have hMarkov := μ.prob_ge_le_expect_div U
    (fun ω => Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω ∧ ¬ C i ω)))
    (show 0 < 3*μ.eventMean E/4 by linarith)
  have hquot : μ.expect U / (3*μ.eventMean E/4) ≤ 2*t/3 := by
    apply (div_le_iff₀ (show 0 < 3*μ.eventMean E/4 by linarith)).mpr
    nlinarith
  have hunion := μ.prob_or_le (fun ω => eventCount E ω < 7*μ.eventMean E/8)
    (fun ω => 3*μ.eventMean E/4 ≤ U ω)
  have hlow := hind.lower_tail
  linarith

def listCaptures (Z : Ω → Option A) (L : Ω → Finset A) (ω : Ω) : Prop :=
  Z ω = none ∨ ∃ a, Z ω = some a ∧ a ∈ L ω

/-- The finite union argument that turns simultaneous capture into one
fixed short list. The sampled output can depend on all the lists. -/
theorem fixed_list_from_many_captures (μ : FiniteProb Ω) (Z : Ω → Option A)
    (L : I → Ω → Finset A) (E : I → Ω → Prop) (B : Finset A) (a : ℝ)
    {u v : ℝ}
    (hcapture : μ.prob (fun ω => eventCount (fun i ω => E i ω ∧ listCaptures Z (L i) ω) ω < a) ≤ u)
    (hfrequent : μ.prob (fun ω => ∃ b, b ∉ B ∧ a ≤ eventCount (fun i ω => b ∈ L i ω) ω) ≤ v) :
    (μ.map Z).listTail B ≤ u + v := by
  rw [listTail_prob, μ.prob_map]
  have hsub := μ.prob_mono (p := fun ω => ∃ b, Z ω = some b ∧ b ∉ B)
    (q := fun ω => eventCount (fun i ω => E i ω ∧ listCaptures Z (L i) ω) ω < a ∨
      ∃ b, b ∉ B ∧ a ≤ eventCount (fun i ω => b ∈ L i ω) ω) (by
      intro ω hω
      obtain ⟨b, hZ, hb⟩ := hω
      by_cases hc : eventCount (fun i ω => E i ω ∧ listCaptures Z (L i) ω) ω < a
      · exact Or.inl hc
      · right
        refine ⟨b, hb, (le_of_not_gt hc).trans ?_⟩
        apply Finset.sum_le_sum
        intro i _
        apply bit_mono
        intro hi
        rcases hi.2 with hnone | ⟨b', hb', hmem⟩
        · simp [hZ] at hnone
        · have he : b = b' := Option.some.inj (hZ.symm.trans hb')
          exact he ▸ hmem)
  have hu := μ.prob_or_le
    (fun ω => eventCount (fun i ω => E i ω ∧ listCaptures Z (L i) ω) ω < a)
    (fun ω => ∃ b, b ∉ B ∧ a ≤ eventCount (fun i ω => b ∈ L i ω) ω)
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/BranchParameters.lean ===== -/

/-! Explicit real inequalities for the independent-list argument.
There are no natural-number floors, subtractions, or asymptotic hypotheses. -/

namespace MISLocal
noncomputable section

theorem exp_neg_nat_log {D : ℝ} (hD : 0 < D) (n : ℕ) :
    Real.exp (-(n : ℝ) * Real.log D) = 1 / D^n := by
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hD, one_div]

theorem branch_parameter_estimates {D ell M C ν t : ℝ}
    (hD : 12 ≤ D) (hlog : 1 ≤ Real.log D) (hM : 0 < M)
    (hellM : 32*ell ≤ M) (hC0 : 0 ≤ C) (hC : C ≤ ell*ν)
    (hCmax : C ≤ D^4) (hν : 256*Real.log D ≤ ν) (ht : 1/D ≤ t) :
    1 ≤ ν/8 ∧ Real.exp (-ν/128) ≤ t/12 ∧
      4*C*Real.exp (2*C/M-ν/8) ≤ t/8 := by
  have hDp : 0 < D := by linarith
  have hν0 : 0 ≤ ν := by linarith
  have hsmall : Real.exp (-ν/128) ≤ 1/D^2 := by
    calc
      _ ≤ Real.exp (-(2:ℝ)*Real.log D) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := exp_neg_nat_log hDp 2
  have hDsmall : (1:ℝ)/D^2 ≤ (1/D)/12 := by
    calc
      _ ≤ 1/(12*D) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ = _ := by ring
  have hCM : 2*C/M ≤ ν/16 := by
    apply (div_le_iff₀ hM).mpr
    nlinarith [mul_le_mul_of_nonneg_right hellM hν0]
  have hexp : Real.exp (2*C/M-ν/8) ≤ 1/D^16 := by
    calc
      _ ≤ Real.exp (-(16:ℝ)*Real.log D) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := exp_neg_nat_log hDp 16
  have hpow : (32:ℝ) ≤ D^11 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (show (2:ℝ) ≤ D by linarith) 11
    norm_num at h
    linarith
  have hlarge : 4*D^4/D^16 ≤ 1/(8*D) := by
    apply (div_le_div_iff₀ (pow_pos hDp 16) (by positivity : 0 < 8*D)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hpow (pow_nonneg hDp.le 5)]
  refine ⟨by linarith, hsmall.trans (hDsmall.trans (by linarith)), ?_⟩
  calc
    _ ≤ 4*C*(1/D^16) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 4*D^4/D^16 := by
      simpa [div_eq_mul_inv, mul_assoc] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCmax (by norm_num : (0:ℝ) ≤ 4))
          (inv_nonneg.mpr (pow_nonneg hDp.le 16))
    _ ≤ 1/(8*D) := hlarge
    _ ≤ t/8 := by rw [show (1:ℝ)/(8*D) = (1/D)/8 by ring]; linarith

end
end MISLocal


/- ===== Source: MISLocal/BranchTransfer.lean ===== -/

/-!
# Relative branch transfer

This proves the independent-branch lemma for actual conditional probabilities.
The output is arbitrary and may be coupled to every input. Eligibility and
the maximizing lists are constructed, rather than supplied as premises.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω I A B : Type*} [Fintype Ω] [Fintype I] [Fintype A] [Fintype B]

def branchEligible (μ : FiniteProb Ω) (X : I → Ω → B) (Z : Ω → Option A)
    (ell : ℕ) (t : ℝ) (i : I) (b : B) : Prop :=
  ((μ.given (X i) b).map Z).tail ell < t/2

def branchList (μ : FiniteProb Ω) (X : I → Ω → B) (Z : Ω → Option A)
    (ell : ℕ) (t : ℝ) (i : I) (b : B) : Finset A :=
  if μ.branchEligible X Z ell t i b then ((μ.given (X i) b).map Z).outputList ell else ∅

omit [Fintype Ω] [Fintype A] in
theorem not_listCaptures_iff (Z : Ω → Option A) (L : Ω → Finset A) (ω : Ω) :
    ¬ listCaptures Z L ω ↔ ∃ a, Z ω = some a ∧ a ∉ L ω := by
  cases h : Z ω <;> simp [listCaptures, h]

omit [Fintype I] in
theorem branch_miss_probability (μ : FiniteProb Ω) (X : I → Ω → B)
    (Z : Ω → Option A) (ell : ℕ) (t : ℝ) (i : I) :
    μ.prob (fun ω => μ.branchEligible X Z ell t i (X i ω) ∧
      ¬ listCaptures Z (fun ω => μ.branchList X Z ell t i (X i ω)) ω) ≤
      t/2 * μ.prob (fun ω => μ.branchEligible X Z ell t i (X i ω)) := by
  let eligible := μ.branchEligible X Z ell t i
  let lists := μ.branchList X Z ell t i
  have hind : μ.prob (fun ω => eligible (X i ω) ∧
      ∃ a, Z ω = some a ∧ a ∉ lists (X i ω)) =
      ∑ b, (μ.map (X i)).weight b * (μ.given (X i) b).prob
        (fun ω => eligible b ∧ ∃ a, Z ω = some a ∧ a ∉ lists b) :=
    (μ.prob_indexed_conditioning (X i)
      (fun b ω => eligible b ∧ ∃ a, Z ω = some a ∧ a ∉ lists b)).symm
  simp_rw [not_listCaptures_iff]
  change μ.prob (fun ω => eligible (X i ω) ∧ ∃ a, Z ω = some a ∧ a ∉ lists (X i ω)) ≤ _
  rw [hind]
  have hpoint (b : B) : (μ.given (X i) b).prob
      (fun ω => eligible b ∧ ∃ a, Z ω = some a ∧ a ∉ lists b) ≤ t/2 * bit (eligible b) := by
    by_cases hb : eligible b
    · simp only [hb, true_and, bit, if_true, mul_one]
      have hl : lists b = ((μ.given (X i) b).map Z).outputList ell := by
        simp only [lists, branchList, show μ.branchEligible X Z ell t i b from hb, if_true]
      rw [hl, ← (μ.given (X i) b).prob_map Z
        (fun z => ∃ a, z = some a ∧ a ∉ ((μ.given (X i) b).map Z).outputList ell),
        ← listTail_prob]
      exact le_of_lt hb
    · simp [hb, bit]
  calc
    _ ≤ ∑ b, (μ.map (X i)).weight b * (t/2 * bit (eligible b)) :=
      Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hpoint b) ((μ.map (X i)).nonneg b))
    _ = _ := by
      change (μ.map (X i)).expect (fun b => t/2 * bit (eligible b)) = _
      rw [expect_mul, ← prob, prob_map]

theorem branchList_total_weight (μ : FiniteProb Ω) (X : I → Ω → B)
    (Z : Ω → Option A) (ell : ℕ) (t : ℝ) :
    μ.totalListWeight (fun i ω => μ.branchList X Z ell t i (X i ω)) ≤
      (ell : ℝ) * μ.eventMean (fun i ω => μ.branchEligible X Z ell t i (X i ω)) := by
  rw [μ.totalListWeight_eq]
  have hcard (i : I) (ω : Ω) :
      ((μ.branchList X Z ell t i (X i ω)).card : ℝ) ≤
        (ell : ℝ) * bit (μ.branchEligible X Z ell t i (X i ω)) := by
    by_cases h : μ.branchEligible X Z ell t i (X i ω)
    · simp only [branchList, h, if_true, bit, mul_one]
      exact_mod_cast bestList_card (fun a => ((μ.given (X i) (X i ω)).map Z).weight (some a)) ell
    · simp [branchList, h, bit]
  calc
    _ ≤ ∑ i, μ.expect (fun ω => (ell : ℝ) * bit (μ.branchEligible X Z ell t i (X i ω))) :=
      Finset.sum_le_sum (fun i _ => μ.expect_mono (hcard i))
    _ = _ := by simp only [μ.expect_mul, ← Finset.mul_sum, eventMean, prob]

/-- The expected number of unusually informative branches is at most
`256 log D`. Dividing by `D` gives the uniform-direction probability bound.
All size assumptions are numerical and explicit. -/
theorem branch_transfer (μ : FiniteProb Ω) (X : I → Ω → B) (Z : Ω → Option A)
    (hind : μ.Independent X) (ell M : ℕ)
    (hD : 12 ≤ (Fintype.card I : ℝ)) (hlog : 1 ≤ Real.log (Fintype.card I : ℝ))
    (hM : 0 < M) (hellM : 32 * ell ≤ M)
    (hsize : (M : ℝ) * Fintype.card I ≤ (Fintype.card I : ℝ)^4)
    (ht : 1/(Fintype.card I : ℝ) ≤ (μ.map Z).tail M) :
    (∑ i, μ.prob (fun ω => ((μ.given (X i) (X i ω)).map Z).tail ell < (μ.map Z).tail M/2)) ≤
      256 * Real.log (Fintype.card I : ℝ) := by
  let D : ℝ := Fintype.card I
  let t := (μ.map Z).tail M
  let E : I → Ω → Prop := fun i ω => μ.branchEligible X Z ell t i (X i ω)
  let L : I → Ω → Finset A := fun i ω => μ.branchList X Z ell t i (X i ω)
  let ν := μ.eventMean E
  let C := μ.totalListWeight L
  let S := bestList (μ.labelWeight L) M
  change ν ≤ 256*Real.log D
  by_contra h
  have hν : 256*Real.log D ≤ ν := (lt_of_not_ge h).le
  have hν0 : (0:ℝ) < ν := by dsimp [D] at hν; linarith
  have hDp : 0 < D := by dsimp [D]; linarith
  have ht0 : 0 < t := lt_of_lt_of_le (one_div_pos.mpr hDp) ht
  have hνD : ν ≤ D := by
    calc
      _ ≤ ∑ _i : I, (1:ℝ) := Finset.sum_le_sum (fun i _ => μ.prob_le_one (E i))
      _ = _ := by simp [D]
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun a _ => μ.eventMean_nonneg (fun i ω => a ∈ L i ω))
  have hC : C ≤ (ell:ℝ)*ν := μ.branchList_total_weight X Z ell t
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hellM' : (32:ℝ)*ell ≤ M := by exact_mod_cast hellM
  have hellM'' : (ell:ℝ) ≤ M := by nlinarith [show (0:ℝ) ≤ ell by positivity]
  have hCmax : C ≤ D^4 := by
    have hc1 := mul_le_mul_of_nonneg_left hνD (Nat.cast_nonneg ell)
    have hc2 := mul_le_mul_of_nonneg_right hellM'' hDp.le
    change (M:ℝ)*D ≤ D^4 at hsize
    linarith
  obtain ⟨ha, hsmall, hfreq⟩ := branch_parameter_estimates hD hlog hM' hellM' hC0 hC hCmax hν ht
  have hcap := μ.many_eligible_captures E (fun i => listCaptures Z (L i))
    (hind.events (μ.branchEligible X Z ell t))
    (fun i => μ.branch_miss_probability X Z ell t i) hsmall hν0
  have hfrequent := (μ.frequent_label_bound L (hind.comp (μ.branchList X Z ell t)) hM ha).trans hfreq
  have hfixed := μ.fixed_list_from_many_captures Z L E S (ν/8) hcap hfrequent
  have htail : t ≤ (μ.map Z).listTail S := (μ.map Z).tail_minimal M S (bestList_card _ _)
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/EntropyProduct.lean ===== -/

/-! Product entropies and information revealed by one additional variable. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C T : Type*}
  [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype T]

@[ext] theorem ext {P Q : FiniteProb Ω} (h : ∀ ω, P.weight ω = Q.weight ω) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

@[simp] theorem map_id (μ : FiniteProb Ω) : μ.map id = μ := by
  ext ω
  simp [map, prob, expect, bit]

theorem map_comp (μ : FiniteProb Ω) (X : Ω → A) (f : A → B) :
    (μ.map X).map f = μ.map (fun ω => f (X ω)) := by
  ext b
  exact μ.prob_map X _

theorem entropyOf_same_fibers (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B)
    (h : ∀ ω ω', X ω = X ω' ↔ Y ω = Y ω') : μ.entropyOf X = μ.entropyOf Y := by
  rw [entropyOf_eq_expect, entropyOf_eq_expect]
  apply μ.expect_congr
  intro ω
  exact congrArg (fun p : ℝ => -Real.log p) (μ.prob_congr (fun ω' => h ω' ω))

theorem entropyOf_determined_le (μ : FiniteProb Ω) (Y : Ω → B) (f : B → A) :
    μ.entropyOf (fun ω => f (Y ω)) ≤ μ.entropyOf Y := by
  have h := μ.condEntropy_nonneg Y (fun ω => f (Y ω))
  rw [condEntropy, μ.entropy_pair_comm, μ.entropy_deterministic_pair] at h
  linarith

theorem product_expect (P : FiniteProb A) (Q : FiniteProb B) (f : A × B → ℝ) :
    (P.product Q).expect f = P.expect (fun a => Q.expect (fun b => f (a,b))) := by
  simp only [expect, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem product_map_fst (P : FiniteProb A) (Q : FiniteProb B) :
    (P.product Q).map Prod.fst = P := by
  ext a
  change (P.product Q).expect (fun ab => bit (ab.1 = a)) = _
  rw [product_expect]
  simp only [expect_const]
  simp [expect, bit]

theorem product_map_snd (P : FiniteProb A) (Q : FiniteProb B) :
    (P.product Q).map Prod.snd = Q := by
  ext b
  change (P.product Q).expect (fun ab => bit (ab.2 = b)) = _
  rw [product_expect]
  change P.expect (fun _ => Q.expect (fun b' => bit (b' = b))) = Q.weight b
  have h : Q.expect (fun b' => bit (b' = b)) = Q.weight b := by simp [expect, bit]
  rw [h, expect_const]

theorem dominated_marginalProduct (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    (μ.map (fun ω => (X ω,Y ω))).Dominated ((μ.map X).product (μ.map Y)) := by
  intro ab hab
  have hx := lt_of_lt_of_le hab (μ.prob_mono (fun _ h => congrArg Prod.fst h))
  have hy := lt_of_lt_of_le hab (μ.prob_mono (fun _ h => congrArg Prod.snd h))
  exact mul_pos hx hy

theorem kl_marginalProduct (μ : FiniteProb Ω) (X : Ω → A) (Y : Ω → B) :
    (μ.map (fun ω => (X ω,Y ω))).kl ((μ.map X).product (μ.map Y)) =
      μ.entropyOf X + μ.entropyOf Y - μ.entropyOf (fun ω => (X ω,Y ω)) := by
  change (μ.map (fun ω => (X ω,Y ω))).expect _ = _
  rw [μ.expect_map]
  simp only [entropyOf_eq_expect, ← μ.expect_add, ← μ.expect_sub]
  apply μ.expect_congr_on_support
  intro ω hω
  have hx := ne_of_gt (μ.map_weight_pos X hω)
  have hy := ne_of_gt (μ.map_weight_pos Y hω)
  change Real.log _ - Real.log (_ * _) = _
  rw [Real.log_mul hx hy]
  ring

theorem product_entropy (P : FiniteProb A) (Q : FiniteProb B) :
    (P.product Q).entropy = P.entropy + Q.entropy := by
  have h := (P.product Q).kl_marginalProduct Prod.fst Prod.snd
  have hid : (fun ab : A × B => (ab.1,ab.2)) = id := rfl
  rw [hid, map_id, product_map_fst, product_map_snd] at h
  simp only [kl, sub_self, mul_zero, Finset.sum_const_zero, entropyOf,
    product_map_fst, product_map_snd, map_id] at h
  linarith

/-- Mutual information is the entropy drop caused by revealing `X` after
the previously revealed data `T`. This identity requires no independence. -/
theorem reveal_gain_symm (μ : FiniteProb Ω) (Y : Ω → A) (X : Ω → B) (Z : Ω → T) :
    μ.condEntropy Y Z - μ.condEntropy Y (fun ω => (Z ω,X ω)) =
      μ.condEntropy X Z - μ.condEntropy X (fun ω => (Z ω,Y ω)) := by
  have h1 := μ.entropy_pair_comm Z X
  have h2 := μ.entropy_pair_comm Z Y
  have h3 := μ.entropyOf_same_fibers (fun ω => (Y ω,Z ω,X ω))
    (fun ω => (X ω,Z ω,Y ω)) (by intro ω ω'; simp only [Prod.mk.injEq]; tauto)
  simp only [condEntropy]
  linarith

theorem reveal_gain_nonneg (μ : FiniteProb Ω) (Y : Ω → A) (X : Ω → B) (Z : Ω → T) :
    0 ≤ μ.condEntropy Y Z - μ.condEntropy Y (fun ω => (Z ω,X ω)) :=
  sub_nonneg.mpr (μ.conditioning_reduces Y Z X)

/-- A joint endpoint state gains at least as much information as either
component when a raw input is revealed. -/
theorem reveal_gain_pair (μ : FiniteProb Ω) (Y : Ω → A) (W : Ω → C)
    (X : Ω → B) (Z : Ω → T) :
    μ.condEntropy Y Z - μ.condEntropy Y (fun ω => (Z ω,X ω)) ≤
      μ.condEntropy (fun ω => (Y ω,W ω)) Z -
        μ.condEntropy (fun ω => (Y ω,W ω)) (fun ω => (Z ω,X ω)) := by
  rw [μ.reveal_gain_symm Y X Z, μ.reveal_gain_symm (fun ω => (Y ω,W ω)) X Z]
  have h := μ.conditioning_reduces X (fun ω => (Z ω,Y ω)) W
  have he := μ.entropyOf_same_fibers (fun ω => (X ω,((Z ω,Y ω),W ω)))
    (fun ω => (X ω,(Z ω,(Y ω,W ω)))) (by intro ω ω'; simp only [Prod.mk.injEq]; tauto)
  have he' := μ.entropy_pair_assoc Z Y W
  simp only [condEntropy] at h ⊢
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/RandomMatrix.lean ===== -/

/-! An actual product of independent fair Boolean matrix entries. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω I A B : Type*} [Fintype Ω] [Fintype I] [Fintype A] [Fintype B]

theorem IndependentEvents.half_lower_tail {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) :
    μ.prob (fun ω => eventCount E ω ≤ μ.eventMean E/2) ≤
      Real.exp (-μ.eventMean E/8) := by
  have hnum : Real.exp (-(1:ℝ)) ≤ 3/8 := by
    have hs := Real.sum_le_exp_of_nonneg (x := (1:ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at hs
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    linarith
  have hm := μ.prob_ge_le_expect_div (fun ω => Real.exp (-eventCount E ω))
    (fun ω => (Real.exp_pos _).le) (Real.exp_pos (-μ.eventMean E/2))
  have he := h.exp_expect_le (-(1:ℝ))
  simp only [neg_one_mul] at he
  calc
    _ ≤ μ.prob (fun ω => Real.exp (-μ.eventMean E/2) ≤ Real.exp (-eventCount E ω)) := by
      apply μ.prob_mono
      intro ω hω
      exact Real.exp_le_exp.mpr (by linarith)
    _ ≤ μ.expect (fun ω => Real.exp (-eventCount E ω)) / Real.exp (-μ.eventMean E/2) := hm
    _ ≤ Real.exp ((Real.exp (-1)-1)*μ.eventMean E) / Real.exp (-μ.eventMean E/2) :=
      div_le_div_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp ((Real.exp (-1)-1)*μ.eventMean E + μ.eventMean E/2) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hn := μ.eventMean_nonneg E
      nlinarith)

def fairBits (I : Type*) [Fintype I] [DecidableEq I] : FiniteProb (I → Bool) :=
  pi (fun _ : I => uniform Bool)

theorem fairBits_coordinate [DecidableEq I] (i : I) :
    (fairBits I).prob (fun x => x i = true) = 1/2 := by
  change (pi (fun _ : I => uniform Bool)).expect (fun x => bit (x i = true)) = _
  rw [pi_expect_coordinate (fun _ : I => uniform Bool) i (fun b => bit (b = true))]
  norm_num [uniform, expect, bit, Fintype.sum_bool]

variable [DecidableEq A] [DecidableEq B]

def rectangleCount (S : Finset A) (T : Finset B) (G : A × B → Bool) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ T, bit (G (a,b) = true)

theorem rectangleCount_eq (S : Finset A) (T : Finset B) (G : A × B → Bool) :
    eventCount (fun ab (G : A × B → Bool) => ab.1 ∈ S ∧ ab.2 ∈ T ∧ G ab = true) G =
      rectangleCount S T G := by
  classical
  let E := fun ab : A × B => ab.1 ∈ S ∧ ab.2 ∈ T ∧ G ab = true
  change (∑ ab, bit (E ab)) = _
  have hs := Finset.sum_subset (f := fun ab => bit (E ab)) (Finset.subset_univ (S.product T))
    (fun ab _ hab => by
      have hn : ¬ (ab.1 ∈ S ∧ ab.2 ∈ T) := by simpa using hab
      by_cases ha : ab.1 ∈ S <;> by_cases hb : ab.2 ∈ T <;> simp_all [E, bit])
  rw [← hs]
  calc
    _ = ∑ ab ∈ S.product T, bit (G ab = true) := by
      apply Finset.sum_congr rfl
      intro ab hab
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
      simp [E, ha, hb]
    _ = _ := Finset.sum_product _ _ _

theorem rectangleCount_expect (S : Finset A) (T : Finset B) :
    (fairBits (A × B)).expect (rectangleCount S T) = (S.card : ℝ)*T.card/2 := by
  change (fairBits (A × B)).expect (fun G => ∑ a ∈ S, ∑ b ∈ T, bit (G (a,b) = true)) = _
  rw [expect_sum]
  simp only [expect_sum]
  change (∑ a ∈ S, ∑ b ∈ T, (fairBits (A × B)).prob (fun G => G (a,b) = true)) = _
  simp [fairBits_coordinate]
  ring

theorem rectangle_sparse_probability (S : Finset A) (T : Finset B) :
    (fairBits (A × B)).prob (fun G => rectangleCount S T G ≤ (S.card : ℝ)*T.card/4) ≤
      Real.exp (-((S.card : ℝ)*T.card)/16) := by
  let E := fun ab : A × B => fun G : A × B → Bool => ab.1 ∈ S ∧ ab.2 ∈ T ∧ G ab = true
  have hind : (fairBits (A × B)).IndependentEvents E :=
    (pi_independent (fun _ : A × B => uniform Bool)).events
      (fun ab b => ab.1 ∈ S ∧ ab.2 ∈ T ∧ b = true)
  have hmean : (fairBits (A × B)).eventMean E = (S.card : ℝ)*T.card/2 := by
    rw [← expect_eventCount]
    have he : eventCount E = rectangleCount S T := funext (rectangleCount_eq S T)
    rw [he, rectangleCount_expect]
  have h := hind.half_lower_tail
  simp only [hmean, E, rectangleCount_eq] at h
  convert h using 1 <;> congr 1 <;> first | (funext G; congr 1; ring) | ring

def exceptionalMatrix (ell : ℕ) (G : A × A → Bool) : Prop :=
  ∃ S : {S : Finset A // S.card = ell}, ∃ T : {T : Finset A // T.card = ell},
    rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4

theorem exceptional_matrix_probability (ell : ℕ) :
    (fairBits (A × A)).prob (exceptionalMatrix (A := A) ell) ≤
      (Fintype.card A : ℝ)^(2*ell) * Real.exp (-(ell : ℝ)^2/16) := by
  let μ := fairBits (A × A)
  let sides := {S : Finset A // S.card = ell}
  let q := Real.exp (-(ell : ℝ)^2/16)
  have hpair (S T : sides) : μ.prob (fun G => rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4) ≤ q := by
    have h := rectangle_sparse_probability S.val T.val
    simpa [S.property, T.property, pow_two, q, μ] using h
  have hfirst := μ.prob_exists_le_sum (fun S : sides => fun G =>
    ∃ T : sides, rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4)
  have hsecond (S : sides) := μ.prob_exists_le_sum (fun T : sides => fun G =>
    rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4)
  have hc : (Fintype.card sides : ℝ) ≤ (Fintype.card A : ℝ)^ell := by
    dsimp [sides]
    rw [Fintype.card_finset_len]
    exact_mod_cast Nat.choose_le_pow (Fintype.card A) ell
  calc
    _ ≤ ∑ S : sides, ∑ T : sides,
        μ.prob (fun G => rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4) :=
      hfirst.trans (Finset.sum_le_sum (fun S _ => hsecond S))
    _ ≤ ∑ _S : sides, ∑ _T : sides, q :=
      Finset.sum_le_sum (fun S _ => Finset.sum_le_sum (fun T _ => hpair S T))
    _ = (Fintype.card sides : ℝ)^2*q := by simp; ring
    _ ≤ ((Fintype.card A : ℝ)^ell)^2*q := by gcongr
    _ = _ := by rw [← pow_mul, Nat.mul_comm ell 2]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/Truncation.lean ===== -/

/-! Actual kept/deleted outputs and their conditional atom bounds. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def restrictOutput {A : Type*} (P : A → Prop) (x : Option A) : Option A :=
  match x with
  | none => none
  | some a => if P a then some a else none

theorem restrictOutput_eq_some {A : Type*} (P : A → Prop) (x : Option A) (a : A) :
    restrictOutput P x = some a ↔ x = some a ∧ P a := by
  cases x with
  | none => simp [restrictOutput]
  | some b =>
    by_cases hba : b = a
    · subst b
      by_cases ha : P a <;> simp [restrictOutput, ha]
    · by_cases hb : P b <;> simp [restrictOutput, hb, hba]

theorem restrictOutput_partition {A : Type*} (P : A → Prop) (x : Option A) :
    bit (restrictOutput P x ≠ none) + bit (restrictOutput (fun a => ¬P a) x ≠ none) =
      bit (x ≠ none) := by
  cases x with
  | none => simp [restrictOutput, bit]
  | some a => by_cases h : P a <;> simp [restrictOutput, bit, h]

theorem restricted_conflicts {A B : Type*} (E : A → B → Prop)
    (P : A → Prop) (Q : B → Prop) (x : Option A) (y : Option B) :
    bit (selectedConflict (fun _ : Unit => E) ((), restrictOutput P x, restrictOutput Q y)) +
      bit (selectedConflict (fun _ : Unit => E)
        ((), restrictOutput (fun a => ¬ P a) x, restrictOutput (fun b => ¬ Q b) y)) ≤
      bit (selectedConflict (fun _ : Unit => E) ((),x,y)) := by
  cases x with
  | none => simp [restrictOutput, selectedConflict, bit]
  | some a =>
    cases y with
    | none => simp [restrictOutput, selectedConflict, bit]
    | some b =>
      by_cases hp : P a <;> by_cases hq : Q b <;> by_cases he : E a b <;>
        simp [restrictOutput, selectedConflict, bit, hp, hq, he]

namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem given_support_eq (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) {ω : Ω} (hω : 0 < (μ.given Y b).weight ω) :
    Y ω = b := by
  by_contra h
  rw [given_weight μ Y b hb] at hω
  simp [bit, h] at hω

theorem given_prob_congr (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) (E F : Ω → Prop)
    (h : ∀ ω, Y ω = b → (E ω ↔ F ω)) :
    (μ.given Y b).prob E = (μ.given Y b).prob F := by
  apply (μ.given Y b).expect_congr_on_support
  intro ω hω
  exact congrArg bit (propext (h ω (μ.given_support_eq Y b hb hω)))

def keptOutput (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B) (m : ℕ) (ω : Ω) : Option A :=
  restrictOutput (fun a => a ∈ ((μ.given Y (Y ω)).map Z).outputList m) (Z ω)

def deletedOutput (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B) (m : ℕ) (ω : Ω) : Option A :=
  restrictOutput (fun a => a ∉ ((μ.given Y (Y ω)).map Z).outputList m) (Z ω)

theorem kept_deleted_mass (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B) (m : ℕ) :
    μ.prob (fun ω => μ.keptOutput Z Y m ω ≠ none) +
      μ.prob (fun ω => μ.deletedOutput Z Y m ω ≠ none) = μ.prob (fun ω => Z ω ≠ none) := by
  rw [prob, prob, ← μ.expect_add]
  exact μ.expect_congr (fun ω => restrictOutput_partition _ (Z ω))

theorem deleted_given_atom (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B)
    (m : ℕ) (b : B) (hb : 0 < (μ.map Y).weight b) (a : A) :
    ((μ.given Y b).map (μ.deletedOutput Z Y m)).weight (some a) =
      if a ∈ ((μ.given Y b).map Z).outputList m then 0 else ((μ.given Y b).map Z).weight (some a) := by
  change (μ.given Y b).prob (fun ω => μ.deletedOutput Z Y m ω = some a) = _
  rw [μ.given_prob_congr Y b hb _ (fun ω => Z ω = some a ∧ a ∉ ((μ.given Y b).map Z).outputList m)
    (by intro ω hω; simp only [deletedOutput, hω, restrictOutput_eq_some])]
  by_cases ha : a ∈ ((μ.given Y b).map Z).outputList m
  · simp only [ha, not_true_eq_false, and_false, if_true, prob_false]
  · simp only [ha, not_false_eq_true, and_true, if_false]
    rfl

theorem deleted_given_atom_le (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B)
    {m : ℕ} (hm : 0 < m) (b : B) (hb : 0 < (μ.map Y).weight b) (a : A) :
    ((μ.given Y b).map (μ.deletedOutput Z Y m)).weight (some a) ≤ 1/(m : ℝ) := by
  rw [μ.deleted_given_atom Z Y m b hb a]
  by_cases ha : a ∈ ((μ.given Y b).map Z).outputList m
  · simp only [ha, if_true]; positivity
  · simp only [ha, if_false]
    exact outside_outputList_le _ m hm ha

theorem kept_given_support (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B)
    (m : ℕ) (b : B) (hb : 0 < (μ.map Y).weight b) (a : A)
    (ha : a ∉ ((μ.given Y b).map Z).outputList m) :
    ((μ.given Y b).map (μ.keptOutput Z Y m)).weight (some a) = 0 := by
  change (μ.given Y b).prob (fun ω => μ.keptOutput Z Y m ω = some a) = _
  rw [μ.given_prob_congr Y b hb _ (fun _ => False) (by
    intro ω hω
    simp only [keptOutput, hω, restrictOutput_eq_some, ha, and_false])]
  exact prob_false _

theorem tail_lower_of_atom_bound (P : FiniteProb (Option A)) (M : ℕ) {c : ℝ}
    (hc : 0 ≤ c) (hatom : ∀ a, P.weight (some a) ≤ c) :
    P.prob (fun a => a ≠ none) - (M : ℝ)*c ≤ P.tail M := by
  change _ ≤ P.listTail (P.outputList M)
  rw [P.listTail_eq]
  have hs := Finset.sum_le_sum (s := P.outputList M) (fun a _ => hatom a)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hcard : ((P.outputList M).card : ℝ) ≤ M := by exact_mod_cast bestList_card _ M
  have hm := mul_le_mul_of_nonneg_right hcard hc
  linarith

theorem deleted_given_tail_lower (μ : FiniteProb Ω) (Z : Ω → Option A) (Y : Ω → B)
    {m : ℕ} (hm : 0 < m) (M : ℕ) (b : B) (hb : 0 < (μ.map Y).weight b) :
    (μ.given Y b).prob (fun ω => μ.deletedOutput Z Y m ω ≠ none) - (M : ℝ)/m ≤
      ((μ.given Y b).map (μ.deletedOutput Z Y m)).tail M := by
  have h := (((μ.given Y b).map (μ.deletedOutput Z Y m))).tail_lower_of_atom_bound M
    (show 0 ≤ (1:ℝ)/m by positivity) (μ.deleted_given_atom_le Z Y hm b hb)
  simpa [prob_map, div_eq_mul_inv] using h

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/ScalarEntropy.lean ===== -/

/-! Scalar neighboring-output estimate from an edge/vertex entropy inequality. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def binaryEntropy (p : ℝ) : ℝ := Real.negMulLog p + Real.negMulLog (1-p)

theorem binaryEntropy_le_rare {p : ℝ} (hp : p ≤ 1) :
    binaryEntropy p ≤ p + Real.negMulLog p := by
  have h := negMulLog_tangent (show 0 ≤ 1-p by linarith) (by norm_num : (0:ℝ) < 1)
  simp only [Real.log_one, mul_zero] at h
  unfold binaryEntropy
  linarith

theorem binaryEntropy_le_two_log {p D : ℝ}
    (hD : 0 < D) (hlog : 1 ≤ Real.log D) (hp : 1/D ≤ p) (hp1 : p ≤ 1) :
    binaryEntropy p ≤ 2*p*Real.log D := by
  have hpp : 0 < p := lt_of_lt_of_le (one_div_pos.mpr hD) hp
  have hpl := Real.log_le_log (one_div_pos.mpr hD) hp
  simp only [one_div, Real.log_inv] at hpl
  have h := binaryEntropy_le_rare hp1
  simp only [Real.negMulLog] at h
  nlinarith [mul_le_mul_of_nonneg_left hpl hpp.le,
    mul_le_mul_of_nonneg_left hlog hpp.le]

namespace FiniteProb

variable {Ω : Type*} [Fintype Ω]

theorem bool_entropy (P : FiniteProb Bool) : P.entropy = binaryEntropy (P.weight true) := by
  have ht := P.total
  simp only [Fintype.sum_bool] at ht
  have hf : P.weight false = 1-P.weight true := by linarith
  simp [entropy, Fintype.sum_bool, binaryEntropy, hf, add_comm]

theorem scalar_pair_overlap (μ : FiniteProb Ω) (U V : Ω → Bool) {D p : ℝ}
    (hD : 0 < D) (hu : μ.prob (fun ω => U ω = true) = p)
    (hv : μ.prob (fun ω => V ω = true) = p)
    (htree : (D/2)*μ.entropyOf (fun ω => (U ω,V ω)) ≥ (D-1)*μ.entropyOf U) :
    p^2/2 - 2*binaryEntropy p/D ≤ μ.prob (fun ω => U ω = true ∧ V ω = true) := by
  let P := μ.map (fun ω => (U ω,V ω))
  let Q := (μ.map U).product (μ.map V)
  have hhu : μ.entropyOf U = binaryEntropy p := by
    change (μ.map U).entropy = _
    rw [bool_entropy]
    exact congrArg binaryEntropy hu
  have hhv : μ.entropyOf V = binaryEntropy p := by
    change (μ.map V).entropy = _
    rw [bool_entropy]
    exact congrArg binaryEntropy hv
  have hkl : P.kl Q ≤ 2*binaryEntropy p/D := by
    rw [show P.kl Q = μ.entropyOf U + μ.entropyOf V - μ.entropyOf (fun ω => (U ω,V ω)) from
      μ.kl_marginalProduct U V, hhu, hhv]
    rw [hhu] at htree
    apply (le_div_iff₀ hD).mpr
    nlinarith
  have hQ : Q.prob (fun ab => ab.1 = true ∧ ab.2 = true) = p^2 := by
    change ((μ.map U).product (μ.map V)).prob _ = _
    simp only [prob, expect, product, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [bit, Bool.false_eq_true, false_and, true_and, and_false,
      if_false, if_true, mul_zero, mul_one, add_zero, zero_add]
    change μ.prob (fun ω => U ω = true) * μ.prob (fun ω => V ω = true) = _
    rw [hu, hv, pow_two]
  have he := P.event_le_two_mul_add_kl Q (μ.dominated_marginalProduct U V)
    (fun ab => ab.1 = true ∧ ab.2 = true)
  rw [hQ] at he
  have hP : P.prob (fun ab => ab.1 = true ∧ ab.2 = true) =
      μ.prob (fun ω => U ω = true ∧ V ω = true) := μ.prob_map _ _
  rw [hP] at he
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/TruncationNumerics.lean ===== -/

/-! Numerical solution of the truncation moment inequality. -/

namespace MISLocal
noncomputable section

theorem quadratic_upper_bound {x b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x^2 ≤ b*x+c^2) : x ≤ b+c := by
  by_contra hn
  have hp := lt_of_not_ge hn
  have hprod := mul_pos (sub_pos.mpr hp) (show 0 < x+c by linarith)
  nlinarith [mul_nonneg hb hc]

theorem truncation_moment_bound {D μ τ w q : ℝ}
    (hD : 0 < D) (hlog : 1 ≤ Real.log D) (hμ1 : μ ≤ 1)
    (hw : 0 ≤ w) (hq : q ≤ 1/D^2) (hmass : τ ≤ 2*μ+2/D)
    (hmoment : μ^2/2 - 2*binaryEntropy μ/D ≤ 4*w+q+2*(256*Real.log D/D)*μ) :
    τ ≤ 2100*Real.log D/D + 6*Real.sqrt w := by
  have hinv : 0 < 1/D := one_div_pos.mpr hD
  have hbase : 1/D ≤ Real.log D/D := div_le_div_of_nonneg_right hlog hD.le
  have hs := Real.sqrt_nonneg w
  by_cases hμ : 1/D ≤ μ
  · have hent := binaryEntropy_le_two_log hD hlog hμ hμ1
    have he := div_le_div_of_nonneg_right hent hD.le
    have hquad : μ^2 ≤ (1032*Real.log D/D)*μ + 8*w+2*q := by
      simp only [div_eq_mul_inv] at hmoment he ⊢
      nlinarith
    have hs2 := Real.sq_sqrt hw
    have hinv2 : (1/D)^2 = (1:ℝ)/D^2 := by ring
    have hc : 8*w+2*q ≤ (3*Real.sqrt w+2/D)^2 := by
      simp only [div_eq_mul_inv, ← inv_pow, one_mul] at hq ⊢
      nlinarith [mul_nonneg hs (inv_nonneg.mpr hD.le), sq_nonneg D⁻¹]
    have hμbound := quadratic_upper_bound
      (show 0 ≤ 1032*Real.log D/D by positivity)
      (show 0 ≤ 3*Real.sqrt w+2/D by positivity) (hquad.trans (by linarith))
    simp only [div_eq_mul_inv] at hμbound hmass hbase hinv ⊢
    nlinarith
  · have hμ' := le_of_not_ge hμ
    simp only [div_eq_mul_inv] at hμ' hmass hbase hinv ⊢
    nlinarith

end
end MISLocal


/- ===== Source: MISLocal/ProductSources.lean ===== -/

/-! Independence of one source from arbitrary functions of all other sources. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C I : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
  [Fintype I] [DecidableEq I]

theorem nonempty (P : FiniteProb Ω) : Nonempty Ω := by
  by_contra h
  haveI : IsEmpty Ω := not_nonempty_iff.mp h
  have ht := P.total
  simp at ht

theorem map_equiv_weight (μ : FiniteProb Ω) (e : Ω ≃ A) (a : A) :
    (μ.map e).weight a = μ.weight (e.symm a) := by
  change μ.prob (fun ω => e ω = a) = _
  rw [μ.prob_congr (fun ω => e.apply_eq_iff_eq_symm_apply)]
  simp [prob, expect, bit]

theorem entropyOf_map (μ : FiniteProb Ω) (X : Ω → A) (f : A → B) :
    (μ.map X).entropyOf f = μ.entropyOf (fun ω => f (X ω)) := by
  unfold entropyOf
  rw [map_comp]

theorem condEntropy_map (μ : FiniteProb Ω) (X : Ω → A) (f : A → B) (g : A → C) :
    (μ.map X).condEntropy f g = μ.condEntropy (fun ω => f (X ω)) (fun ω => g (X ω)) := by
  simp only [condEntropy, entropyOf_map]

theorem pi_splitAt {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (i : I) :
    (pi P).map (Equiv.piSplitAt i T) =
      (P i).product (pi (fun j : {j // j ≠ i} => P j.val)) := by
  ext ab
  rw [map_equiv_weight]
  change (∏ j, (P j).weight ((Equiv.piSplitAt i T).symm ab j)) =
    (P i).weight ab.1 * ∏ j : {j // j ≠ i}, (P j.val).weight (ab.2 j)
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  congr 1
  · simp [Equiv.piSplitAt]
  · apply Finset.prod_congr rfl
    intro j _
    simp [Equiv.piSplitAt, j.property]

theorem product_map_second (P : FiniteProb A) (Q : FiniteProb B) (f : B → C) :
    (P.product Q).map (fun ab => (ab.1,f ab.2)) = P.product (Q.map f) := by
  ext ac
  change (P.product Q).expect (fun ab => bit ((ab.1,f ab.2) = ac)) = _
  rw [product_expect]
  have he (a : A) (b : B) : bit ((a,f b) = ac) = bit (a = ac.1) * bit (f b = ac.2) := by
    by_cases ha : a = ac.1 <;> by_cases hb : f b = ac.2 <;> simp [bit, Prod.ext_iff, ha, hb]
  simp only [he, expect_mul]
  change P.expect (fun a => bit (a = ac.1) * (Q.map f).weight ac.2) = _
  simp [expect, bit, product]

theorem product_condEntropy_first_second (P : FiniteProb A) (Q : FiniteProb B) (f : B → C) :
    (P.product Q).condEntropy Prod.fst (fun ab => f ab.2) = P.entropy := by
  have hg : (P.product Q).map (fun ab => f ab.2) = Q.map f := by
    rw [← map_comp _ Prod.snd f, product_map_snd]
  simp only [condEntropy, entropyOf, product_map_second, hg, product_entropy]
  ring

/-- A source does not influence a function when changing only that source
leaves the function unchanged. This is a pointwise locality statement. -/
def DoesNotRead {T : I → Type*} (Y : (∀ i, T i) → A) (i : I) : Prop :=
  ∀ x y, (∀ j, j ≠ i → x j = y j) → Y x = Y y

theorem coordinate_condEntropy {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (i : I) (Y : (∀ i, T i) → A)
    (hY : DoesNotRead Y i) :
    (pi P).condEntropy (fun x => x i) Y = (P i).entropy := by
  let ai : T i := Classical.choice (P i).nonempty
  let f : (∀ j : {j // j ≠ i}, T j.val) → A :=
    fun z => Y ((Equiv.piSplitAt i T).symm (ai,z))
  have hf (x : ∀ i, T i) : Y x = f (fun j => x j.val) := by
    apply hY
    intro j hj
    simp [Equiv.piSplitAt, hj]
  have hm := (pi P).condEntropy_map (Equiv.piSplitAt i T) Prod.fst (fun ab => f ab.2)
  rw [pi_splitAt, product_condEntropy_first_second] at hm
  have he : (fun x => f (fun j => x j.val)) = Y := funext (fun x => (hf x).symm)
  simpa only [Equiv.piSplitAt_apply, he] using hm.symm

theorem condEntropy_same_fibers (μ : FiniteProb Ω) (X : Ω → A)
    (Y : Ω → B) (Z : Ω → C) (h : ∀ ω ω', Y ω = Y ω' ↔ Z ω = Z ω') :
    μ.condEntropy X Y = μ.condEntropy X Z := by
  have hj := μ.entropyOf_same_fibers (fun ω => (X ω,Y ω)) (fun ω => (X ω,Z ω))
    (by intro ω ω'; simp only [Prod.mk.injEq, h ω ω'])
  simp only [condEntropy, hj, μ.entropyOf_same_fibers Y Z h]

/-- Conditioning on finer data reduces entropy. Refinement is expressed by
equality of observations, avoiding arbitrary choices on unattained values. -/
theorem condEntropy_refinement (μ : FiniteProb Ω) (X : Ω → A)
    (Y : Ω → B) (Z : Ω → C) (h : ∀ ω ω', Z ω = Z ω' → Y ω = Y ω') :
    μ.condEntropy X Z ≤ μ.condEntropy X Y := by
  have he := μ.condEntropy_same_fibers X (fun ω => (Y ω,Z ω)) Z (by
    intro ω ω'
    simp only [Prod.mk.injEq]
    exact ⟨And.right, fun hz => ⟨h ω ω' hz,hz⟩⟩)
  rw [← he]
  exact μ.conditioning_reduces X Y Z

theorem condEntropy_of_determined (μ : FiniteProb Ω) (X : Ω → A)
    (Y : Ω → B) (h : ∀ ω ω', Y ω = Y ω' → X ω = X ω') :
    μ.condEntropy X Y = 0 := by
  have he := μ.entropyOf_same_fibers (fun ω => (X ω,Y ω)) Y (by
    intro ω ω'
    simp only [Prod.mk.injEq]
    exact ⟨And.right, fun hy => ⟨h ω ω' hy,hy⟩⟩)
  simp only [condEntropy, he, sub_self]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/RevealedEntropy.lean ===== -/

/-!
# Revealing finitely many independent sources

Observations are literal coordinate restrictions, represented by `Option` at
each coordinate. Revealing a source is set insertion; every entropy identity
is proved for this representation and the actual product probability space.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

variable {I : Type*} [DecidableEq I] {T : I → Type*}

def observeInputs (S : Finset I) (x : ∀ i, T i) : ∀ i, Option (T i) :=
  fun i => if i ∈ S then some (x i) else none

theorem observeInputs_eq_iff (S : Finset I) (x y : ∀ i, T i) :
    observeInputs S x = observeInputs S y ↔ ∀ i ∈ S, x i = y i := by
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa only [observeInputs, hi, if_true, Option.some.injEq] using he
  · intro h
    funext i
    by_cases hi : i ∈ S <;> simp [observeInputs, hi, h i]

theorem observeInputs_insert_fibers (S : Finset I) (i : I) (x y : ∀ i, T i) :
    observeInputs (insert i S) x = observeInputs (insert i S) y ↔
      (observeInputs S x,x i) = (observeInputs S y,y i) := by
  simp only [observeInputs_eq_iff, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Finset.mem_insert_of_mem hj), h i (Finset.mem_insert_self _ _)⟩
  · rintro ⟨hS,hi⟩ j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact hS j hj

theorem observeInputs_doesNotRead (S : Finset I) (i : I) (hi : i ∉ S) :
    FiniteProb.DoesNotRead (observeInputs (T := T) S) i := by
  intro x y hxy
  apply (observeInputs_eq_iff S x y).mpr
  intro j hj
  exact hxy j (fun h => hi (h ▸ hj))

namespace FiniteProb

variable [Fintype I] [∀ i, Fintype (T i)] {A B : Type*} [Fintype A] [Fintype B]

def revealGain (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) : ℝ :=
  (pi P).condEntropy Y (observeInputs S) - (pi P).condEntropy Y (observeInputs (insert i S))

theorem revealGain_eq (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) :
    revealGain P Y S i = (pi P).condEntropy Y (observeInputs S) -
      (pi P).condEntropy Y (fun x => (observeInputs S x,x i)) := by
  unfold revealGain
  rw [(pi P).condEntropy_same_fibers Y _ _ (observeInputs_insert_fibers S i)]

theorem revealGain_nonneg (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) : 0 ≤ revealGain P Y S i := by
  rw [revealGain_eq]
  exact (pi P).reveal_gain_nonneg Y (fun x => x i) (observeInputs S)

theorem revealGain_known (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) (hi : i ∈ S) : revealGain P Y S i = 0 := by
  simp only [revealGain, Finset.insert_eq_of_mem hi, sub_self]

theorem revealGain_unread (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset I) (i : I) (hY : DoesNotRead Y i) : revealGain P Y S i = 0 := by
  by_cases hi : i ∈ S
  · exact revealGain_known P Y S i hi
  · rw [revealGain_eq, (pi P).reveal_gain_symm]
    rw [coordinate_condEntropy P i _ (observeInputs_doesNotRead S i hi),
      coordinate_condEntropy P i _ (by
        intro x y hxy
        exact Prod.ext (observeInputs_doesNotRead S i hi x y hxy) (hY x y hxy)), sub_self]

/-- On an edge that has not already observed the source, revealing that
source yields at least the gain at either endpoint. -/
theorem revealGain_refinement (P : ∀ i, FiniteProb (T i))
    (Y : (∀ i, T i) → A) (W : (∀ i, T i) → B)
    (S U : Finset I) (i : I) (hSU : S ⊆ U) (hi : i ∉ U)
    (hYW : ∀ x y, W x = W y → Y x = Y y) :
    revealGain P Y S i ≤ revealGain P W U i := by
  have hiS : i ∉ S := fun h => hi (hSU h)
  rw [revealGain_eq, revealGain_eq,
    (pi P).reveal_gain_symm Y (fun x => x i) (observeInputs S),
    (pi P).reveal_gain_symm W (fun x => x i) (observeInputs U),
    coordinate_condEntropy P i _ (observeInputs_doesNotRead S i hiS),
    coordinate_condEntropy P i _ (observeInputs_doesNotRead U i hi)]
  apply sub_le_sub_left
  apply (pi P).condEntropy_refinement
  intro x y he
  refine Prod.ext ?_ (hYW x y (congrArg Prod.snd he))
  apply (observeInputs_eq_iff S x y).mpr
  intro j hj
  exact (observeInputs_eq_iff U x y).mp (congrArg Prod.fst he) j (hSU hj)

end FiniteProb

def revealPrefix {n : ℕ} (t : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < t)

@[simp] theorem revealPrefix_zero {n : ℕ} : revealPrefix (n := n) 0 = ∅ := by
  ext i
  simp [revealPrefix]

@[simp] theorem revealPrefix_full (n : ℕ) : revealPrefix (n := n) n = Finset.univ := by
  ext i
  simp [revealPrefix, i.isLt]

theorem revealPrefix_succ {n : ℕ} (i : Fin n) :
    revealPrefix (i.val+1) = insert i (revealPrefix i.val) := by
  ext j
  simp only [revealPrefix, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

theorem self_not_revealPrefix {n : ℕ} (i : Fin n) : i ∉ revealPrefix i.val := by
  simp [revealPrefix]

namespace FiniteProb

theorem revealGain_sum {n : ℕ} {T : Fin n → Type*} [∀ i, Fintype (T i)]
    {A : Type*} [Fintype A] (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A)
    (S : Finset (Fin n)) :
    (∑ i, revealGain P Y (S ∪ revealPrefix i.val) i) = (pi P).condEntropy Y (observeInputs S) := by
  let f : ℕ → ℝ := fun t => (pi P).condEntropy Y (observeInputs (S ∪ revealPrefix t))
  have he (i : Fin n) : revealGain P Y (S ∪ revealPrefix i.val) i = f i.val-f (i.val+1) := by
    simp only [revealGain, f, revealPrefix_succ, Finset.union_insert]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun t => f t-f (t+1)) n, Finset.sum_range_sub']
  have hfull : f n = 0 := by
    change (pi P).condEntropy Y (observeInputs (S ∪ revealPrefix n)) = 0
    rw [revealPrefix_full, Finset.union_eq_right.mpr (Finset.subset_univ S)]
    apply (pi P).condEntropy_of_determined
    intro x y hxy
    have heq : x = y := funext (fun i => (observeInputs_eq_iff Finset.univ x y).mp hxy i (Finset.mem_univ i))
    exact congrArg Y heq
  rw [hfull, sub_zero]
  simp [f]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/EntropyCharging.lean ===== -/

/-!
# Conditional edge/vertex entropy from local source charging

This is the finite-source revelation argument: each source's entropy drop is
charged along distinct incident edges. The hypotheses of `SourceCharge` are
purely combinatorial (incidence and coordinate containment), not entropy
inequalities. In a regular tree the charging edges point away from the source.

The revelation method is inspired by Csóka--Harangi--Virág, "Entropy and
expansion", arXiv:1811.09560. The coordinate-conditioned formulation here is
an adaptation for the occupancy argument.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem sum_le_of_charging {V E : Type*} [Fintype V] [Fintype E]
    (active : V → Prop) (d : ℕ) (route : ({v // active v} × Fin d) ↪ E)
    (g : V → ℝ) (h : E → ℝ) (hzero : ∀ v, ¬ active v → g v = 0)
    (hnonneg : ∀ e, 0 ≤ h e) (hcharge : ∀ z, g z.1.val ≤ h (route z)) :
    (d : ℝ) * (∑ v, g v) ≤ ∑ e, h e := by
  have hz : (∑ v : {v // ¬ active v}, g v.val) = 0 :=
    Finset.sum_eq_zero (fun v _ => hzero v.val v.property)
  have hsum := Fintype.sum_subtype_add_sum_subtype active g
  rw [hz, add_zero] at hsum
  have hcount : (∑ z : {v // active v} × Fin d, g z.1.val) = (d : ℝ)*(∑ v, g v) := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hsum]
  rw [← hcount]
  calc
    _ ≤ ∑ z, h (route z) := Finset.sum_le_sum (fun z _ => hcharge z)
    _ = ∑ e ∈ Finset.univ.map route, h e := (Finset.sum_map _ _ _).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _ _ => hnonneg e)

/-- An explicit certificate describing how each source is charged. `reads v`
contains the input coordinates read by the vertex output; `vertexView` and
`edgeView` are the coordinate sets conditioned upon in the desired inequality.
No probability distribution or target conclusion occurs in this structure. -/
structure SourceCharge {I V E : Type*} [DecidableEq I]
    (left right : E → V) (reads vertexView : V → Finset I)
    (edgeView : E → Finset I) (d : ℕ) where
  route : ∀ i : I, ({v // i ∈ reads v ∧ i ∉ vertexView v} × Fin d) ↪ E
  incident : ∀ i z, left (route i z) = z.1.val ∨ right (route i z) = z.1.val
  contains : ∀ i z, vertexView z.1.val ⊆ edgeView (route i z)
  fresh : ∀ i z, i ∉ edgeView (route i z)

namespace FiniteProb

theorem conditional_edge_vertex_entropy {n d : ℕ}
    {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
    {T : Fin n → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (Y : V → (∀ i, T i) → A)
    (left right : E → V) (reads vertexView : V → Finset (Fin n))
    (edgeView : E → Finset (Fin n))
    (hlocal : ∀ v i, i ∉ reads v → DoesNotRead (Y v) i)
    (charge : SourceCharge left right reads vertexView edgeView d) :
    (d : ℝ) * (∑ v, (pi P).condEntropy (Y v) (observeInputs (vertexView v))) ≤
      ∑ e, (pi P).condEntropy (fun x => (Y (left e) x,Y (right e) x))
        (observeInputs (edgeView e)) := by
  have hstep (i : Fin n) :
      (d : ℝ)*(∑ v, revealGain P (Y v) (vertexView v ∪ revealPrefix i.val) i) ≤
        ∑ e, revealGain P (fun x => (Y (left e) x,Y (right e) x))
          (edgeView e ∪ revealPrefix i.val) i := by
    apply sum_le_of_charging (fun v => i ∈ reads v ∧ i ∉ vertexView v) d (charge.route i)
    · intro v hv
      by_cases hi : i ∈ vertexView v
      · exact revealGain_known P (Y v) _ i (Finset.mem_union_left _ hi)
      · exact revealGain_unread P (Y v) _ i (hlocal v i (fun h => hv ⟨h,hi⟩))
    · intro e
      exact revealGain_nonneg P _ _ i
    · intro z
      apply revealGain_refinement P _ _ _ _ i
      · exact Finset.union_subset_union (charge.contains i z) (Finset.Subset.refl _)
      · exact fun h => (Finset.mem_union.mp h).elim (charge.fresh i z) (self_not_revealPrefix i)
      · intro x y hxy
        rcases charge.incident i z with hleft | hright
        · simpa only [hleft] using congrArg Prod.fst hxy
        · simpa only [hright] using congrArg Prod.snd hxy
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep i)
  rw [← Finset.mul_sum, Finset.sum_comm] at hs
  conv_rhs at hs => rw [Finset.sum_comm]
  simpa only [revealGain_sum] using hs

/-- The symmetric regular-graph form. The only additional hypotheses are
vertex/edge symmetry of the displayed entropies and the incidence count.
All entropy inequalities have already been proved from the product sources. -/
theorem symmetric_conditional_edge_entropy {n d : ℕ}
    {V E A : Type*} [Fintype V] [Nonempty V] [Fintype E] [Fintype A]
    {T : Fin n → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (Y : V → (∀ i, T i) → A)
    (left right : E → V) (reads vertexView : V → Finset (Fin n))
    (edgeView : E → Finset (Fin n))
    (hlocal : ∀ v i, i ∉ reads v → DoesNotRead (Y v) i)
    (charge : SourceCharge left right reads vertexView edgeView d)
    (hcard : 2*Fintype.card E = (d+1)*Fintype.card V) {Hv He : ℝ}
    (hv : ∀ v, (pi P).condEntropy (Y v) (observeInputs (vertexView v)) = Hv)
    (he : ∀ e, (pi P).condEntropy (fun x => (Y (left e) x,Y (right e) x))
      (observeInputs (edgeView e)) = He) :
    ((d : ℝ)+1)/2*He ≥ (d : ℝ)*Hv := by
  have h := conditional_edge_vertex_entropy P Y left right reads vertexView edgeView hlocal charge
  simp only [hv, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hc : (Fintype.card E : ℝ) = ((d : ℝ)+1)*(Fintype.card V : ℝ)/2 := by
    have hc' : (2:ℝ)*Fintype.card E = ((d : ℝ)+1)*Fintype.card V := by exact_mod_cast hcard
    linarith
  rw [hc] at h
  have hp : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_left hp).mp
  convert h using 1 <;> ring

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/TreeParent.lean ===== -/

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


/- ===== Source: MISLocal/ParentCharging.lean ===== -/

/-! Constructing an injective source-routing certificate by omitting parent edges. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

variable {I V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]

def edgeIncident (left right : E → V) (v : V) (e : E) : Prop := left e = v ∨ right e = v

/-- Construct the certificate from parent choices. The covering property
for edges between active vertices is supplied by rooted-tree geometry. -/
def sourceChargeOfParents (left right : E → V) (reads vertexView : V → Finset I)
    (edgeView : E → Finset I) (d : ℕ)
    (parent : ∀ i, {v // i ∈ reads v ∧ i ∉ vertexView v} → E)
    (hdegree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1)
    (hparent : ∀ i v, edgeIncident left right v.val (parent i v))
    (hcover : ∀ i (v w : {v // i ∈ reads v ∧ i ∉ vertexView v}), v.val ≠ w.val →
      ∀ e, edgeIncident left right v.val e → edgeIncident left right w.val e →
        e = parent i v ∨ e = parent i w)
    (hinner : ∀ i v e, edgeIncident left right v.val e →
      i ∈ edgeView e → e = parent i v)
    (hcontains : ∀ v e, edgeIncident left right v e → vertexView v ⊆ edgeView e) :
    SourceCharge left right reads vertexView edgeView d := by
  let outgoing := fun i (v : {v // i ∈ reads v ∧ i ∉ vertexView v}) =>
    (Finset.univ.filter (edgeIncident left right v.val)).erase (parent i v)
  have hcard (i : I) (v : {v // i ∈ reads v ∧ i ∉ vertexView v}) :
      (outgoing i v).card = d := by
    dsimp [outgoing]
    rw [Finset.card_erase_of_mem (by simp [hparent i v]), hdegree]
    omega
  let enum := fun i (v : {v // i ∈ reads v ∧ i ∉ vertexView v}) =>
    (Fintype.equivOfCardEq (by simp [hcard i v]) : Fin d ≃ {e // e ∈ outgoing i v})
  let send := fun i (v : {v // i ∈ reads v ∧ i ∉ vertexView v}) (j : Fin d) => (enum i v j).val
  have hsend_inc (i : I) (v : {v // i ∈ reads v ∧ i ∉ vertexView v}) (j : Fin d) :
      edgeIncident left right v.val (send i v j) := by
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp (enum i v j).property).2).2
  have hsend_ne (i : I) (v : {v // i ∈ reads v ∧ i ∉ vertexView v}) (j : Fin d) :
      send i v j ≠ parent i v := (Finset.mem_erase.mp (enum i v j).property).1
  have hinj (i : I) : Function.Injective (fun z : {v // i ∈ reads v ∧ i ∉ vertexView v} × Fin d =>
      send i z.1 z.2) := by
    rintro ⟨v,j⟩ ⟨w,k⟩ heq
    change send i v j = send i w k at heq
    by_cases hvw : v.val = w.val
    · have he : v = w := Subtype.ext hvw
      subst w
      have hsub : enum i v j = enum i v k := Subtype.ext heq
      have hjk := (enum i v).injective hsub
      exact Prod.ext rfl hjk
    · have hwinc : edgeIncident left right w.val (send i v j) := by
        rw [heq]
        exact hsend_inc i w k
      rcases hcover i v w hvw (send i v j) (hsend_inc i v j) hwinc with hp | hp
      · exact False.elim (hsend_ne i v j hp)
      · exact False.elim (hsend_ne i w k (heq.symm.trans hp))
  refine ⟨fun i => ⟨fun z => send i z.1 z.2, hinj i⟩, ?_, ?_, ?_⟩
  · intro i z
    exact hsend_inc i z.1 z.2
  · intro i z
    exact hcontains z.1.val _ (hsend_inc i z.1 z.2)
  · intro i z hi
    exact hsend_ne i z.1 z.2 (hinner i z.1 _ (hsend_inc i z.1 z.2) hi)

end
end MISLocal


/- ===== Source: MISLocal/GeometricCharging.lean ===== -/

/-! Source routing on a finite regular graph whose individual reader regions
are induced trees. The ambient graph is NOT assumed to be a finite regular
tree (which would make the hypotheses impossible at degree at least two). -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

def edgeLeft (e : G.edgeSet) : V := e.val.out.1
def edgeRight (e : G.edgeSet) : V := e.val.out.2

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edge_endpoints (e : G.edgeSet) : s(edgeLeft G e,edgeRight G e) = e.val :=
  Quot.out_eq e.val

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem incident_iff_mem (v : V) (e : G.edgeSet) :
    edgeIncident (edgeLeft G) (edgeRight G) v e ↔ v ∈ e.val := by
  rw [← edge_endpoints G e, Sym2.mem_iff]
  simp only [edgeIncident, eq_comm]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edge_eq_of_incident {v w : V} (hvw : v ≠ w) (e : G.edgeSet)
    (hv : edgeIncident (edgeLeft G) (edgeRight G) v e)
    (hw : edgeIncident (edgeLeft G) (edgeRight G) w e) : e.val = s(v,w) := by
  exact (Sym2.mem_and_mem_iff hvw).mp
    ⟨(incident_iff_mem G v e).mp hv,(incident_iff_mem G w e).mp hw⟩

def regionParent (W : Set V) (ht : (G.induce W).IsTree) (root : W)
    (anchor : G.edgeSet) (v : W) : G.edgeSet :=
  if hv : v = root then anchor else
    (SimpleGraph.Embedding.induce W).toHom.mapEdgeSet (parentEdge ht root ⟨v,hv⟩)

omit [Fintype V] [DecidableRel G.Adj] in
theorem regionParent_incident (W : Set V) (ht : (G.induce W).IsTree) (root : W)
    (anchor : G.edgeSet) (ha : root.val ∈ anchor.val) (v : W) :
    v.val ∈ (regionParent G W ht root anchor v).val := by
  unfold regionParent
  split_ifs with hv
  · simpa [hv] using ha
  · change v.val ∈ s(v.val,(parentDart ht root ⟨v,hv⟩).snd.val)
    exact Sym2.mem_mk_left _ _

omit [Fintype V] [DecidableRel G.Adj] in
theorem regionParent_of_tree_parent (W : Set V) (ht : (G.induce W).IsTree)
    (root : W) (anchor : G.edgeSet) (v w : W) (hv : v ≠ root)
    (hp : (parentEdge ht root ⟨v,hv⟩).val = s(v,w)) :
    (regionParent G W ht root anchor v).val = s(v.val,w.val) := by
  simp only [regionParent, dif_neg hv]
  change Sym2.map Subtype.val (parentEdge ht root ⟨v,hv⟩).val = _
  rw [hp]
  rfl

theorem regionParent_cover (W : Set V) (ht : (G.induce W).IsTree)
    (root : W) (anchor : G.edgeSet) (v w : W) (hvw : G.Adj v.val w.val) :
    (regionParent G W ht root anchor v).val = s(v.val,w.val) ∨
      (regionParent G W ht root anchor w).val = s(v.val,w.val) := by
  rcases edge_has_parent_endpoint ht root v w hvw with ⟨hv,hp⟩ | ⟨hw,hp⟩
  · exact Or.inl (regionParent_of_tree_parent G W ht root anchor v w hv hp)
  · exact Or.inr (by
      rw [Sym2.eq_swap] at hp
      simpa only [Sym2.eq_swap] using
        regionParent_of_tree_parent G W ht root anchor w v hw hp)

theorem regionParent_anchor (W : Set V) (ht : (G.induce W).IsTree)
    (root : W) (anchor : G.edgeSet) (ha : root.val ∈ anchor.val) (v : W)
    (hv : v.val ∈ anchor.val) : regionParent G W ht root anchor v = anchor := by
  by_cases he : v = root
  · simp [regionParent, he]
  · have hne : v.val ≠ root.val := fun h => he (Subtype.ext h)
    have hae : anchor.val = s(v.val,root.val) := (Sym2.mem_and_mem_iff hne).mp ⟨hv,ha⟩
    have hadj : (G.induce W).Adj v root := by
      have h := anchor.property
      rw [hae] at h
      exact h
    rcases edge_has_parent_endpoint ht root v root hadj with ⟨hv',hp⟩ | ⟨hr,_⟩
    · apply Subtype.ext
      rw [regionParent_of_tree_parent G W ht root anchor v root hv' hp, hae]
    · exact False.elim (hr rfl)

/-- Reader regions and their already-observed inner regions are genuine
induced trees/connected sets. These purely geometric assumptions suffice to
CONSTRUCT the source-charge certificate, rather than postulate its routes. -/
def sourceChargeOfReaderTrees {I : Type*} [DecidableEq I]
    (reads vertexView : V → Finset I) (edgeView : G.edgeSet → Finset I) (d : ℕ)
    (root : ∀ i, {v // i ∈ reads v}) (anchor : I → G.edgeSet)
    (ht : ∀ i, (G.induce {v | i ∈ reads v}).IsTree)
    (ha : ∀ i, (root i).val ∈ (anchor i).val)
    (hdegree : ∀ v, (Finset.univ.filter
      (edgeIncident (edgeLeft G) (edgeRight G) v)).card = d+1)
    (hknown : ∀ v, vertexView v ⊆ reads v)
    (hinner : ∀ i v, i ∈ vertexView v →
      i ∈ vertexView (root i).val ∧
        ((G.induce {v | i ∈ reads v}).induce
          {w | i ∈ vertexView w.val}).Connected)
    (hedge : ∀ i e, i ∈ edgeView e →
      i ∈ vertexView (edgeLeft G e) ∨ i ∈ vertexView (edgeRight G e) ∨ e = anchor i)
    (hcontains : ∀ v e, edgeIncident (edgeLeft G) (edgeRight G) v e →
      vertexView v ⊆ edgeView e) :
    SourceCharge (edgeLeft G) (edgeRight G) reads vertexView edgeView d := by
  let parent := fun i (v : {v // i ∈ reads v ∧ i ∉ vertexView v}) =>
    regionParent G {v | i ∈ reads v} (ht i) (root i) (anchor i) ⟨v.val,v.property.1⟩
  apply sourceChargeOfParents (edgeLeft G) (edgeRight G) reads vertexView edgeView d parent hdegree
  · intro i v
    exact (incident_iff_mem G _ _).mpr
      (regionParent_incident G _ (ht i) (root i) (anchor i) (ha i) _)
  · intro i v w hne e hv hw
    have he := edge_eq_of_incident G hne e hv hw
    have hadj : G.Adj v.val w.val := by simpa only [he] using e.property
    rcases regionParent_cover G _ (ht i) (root i) (anchor i)
      ⟨v.val,v.property.1⟩ ⟨w.val,w.property.1⟩ hadj with hp | hp
    · exact Or.inl (Subtype.ext (he.trans hp.symm))
    · exact Or.inr (Subtype.ext (he.trans hp.symm))
  · intro i v e hv hi
    have henter (w : V) (hw : i ∈ vertexView w)
        (hwe : edgeIncident (edgeLeft G) (edgeRight G) w e) : e = parent i v := by
      have hvw : v.val ≠ w := fun h => v.property.2 (h ▸ hw)
      have he := edge_eq_of_incident G hvw e hv hwe
      have hadj : G.Adj v.val w := by simpa only [he] using e.property
      obtain ⟨hroot,hconn⟩ := hinner i w hw
      obtain ⟨hvr,hp⟩ := parent_of_edge_into_connected_set (ht i) (root i)
        {w | i ∈ vertexView w.val} hconn hroot
        (v := ⟨v.val,v.property.1⟩) (w := ⟨w,hknown w hw⟩) v.property.2 hw hadj
      apply Subtype.ext
      exact he.trans (regionParent_of_tree_parent G _ (ht i) (root i) (anchor i)
        ⟨v.val,v.property.1⟩ ⟨w,hknown w hw⟩ hvr hp).symm
    rcases hedge i e hi with hl | hr | he
    · exact henter _ hl (Or.inl rfl)
    · exact henter _ hr (Or.inr rfl)
    · subst e
      exact (regionParent_anchor G _ (ht i) (root i) (anchor i) (ha i)
        ⟨v.val,v.property.1⟩ ((incident_iff_mem G _ _).mp hv)).symm
  · exact hcontains

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/SourceGrouping.lean ===== -/

/-! Disjoint groups of independent coordinates remain jointly independent. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def groupInputs {S J : Type*} {T : S → Type*} (owner : S → J) :
    (∀ s, T s) ≃ (∀ j, ∀ s : {s // owner s = j}, T s.val) where
  toFun x _ s := x s.val
  invFun x s := x (owner s) ⟨s,rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext j s
    rcases s with ⟨s,hs⟩
    cases hs
    rfl

namespace FiniteProb

variable {S J : Type*} {T : S → Type*} [Fintype S] [Fintype J] [∀ s, Fintype (T s)]
  [DecidableEq S] [DecidableEq J]

theorem pi_grouped (P : ∀ s, FiniteProb (T s)) (owner : S → J) :
    (pi P).map (groupInputs (T := T) owner) =
      pi (fun j => pi (fun s : {s // owner s = j} => P s.val)) := by
  ext x
  rw [map_equiv_weight]
  change (∏ s, (P s).weight (x (owner s) ⟨s,rfl⟩)) =
    ∏ j, ∏ s : {s // owner s = j}, (P s.val).weight (x j s)
  rw [← Fintype.prod_fiberwise owner (fun s => (P s).weight (x (owner s) ⟨s,rfl⟩))]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  rintro ⟨s,hs⟩ _
  cases hs
  rfl

theorem grouped_independent (P : ∀ s, FiniteProb (T s)) (owner : S → J) :
    (pi P).Independent (fun j x => (fun s : {s // owner s = j} => x s.val)) := by
  have h : ((pi P).map (groupInputs (T := T) owner)).Independent (fun j x => x j) := by
    rw [pi_grouped]
    exact pi_independent _
  simpa only [Independent, expect_map] using h

theorem Independent.option_some {Ω I : Type*} [Fintype Ω] [Fintype I]
    {T : Option I → Type*} {μ : FiniteProb Ω} {X : ∀ i, Ω → T i}
    (h : μ.Independent X) : μ.Independent (fun i : I => X (some i)) := by
  intro f
  have he := h (fun i => match i with | none => fun _ => (1:ℝ) | some i => f i)
  simpa only [Fintype.prod_option, one_mul, expect_const] using he

/-- Coordinates with owner `none` may contain private randomness or unused
inputs. Arbitrary functions of the disjoint remaining blocks are independent. -/
theorem disjoint_blocks_independent {B : J → Type*} (P : ∀ s, FiniteProb (T s))
    (owner : S → Option J) (f : ∀ j, (∀ s : {s // owner s = some j}, T s.val) → B j) :
    (pi P).Independent (fun j x => f j (fun s => x s.val)) :=
  ((grouped_independent P owner).option_some).comp f

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/ConditionalSources.lean ===== -/

/-!
# Coordinate conditioning preserves a product distribution

On each positive observation fiber, observed coordinates become point masses
and the other coordinates keep their original distributions. The result
applies to arbitrary finite coordinate types and real probability weights.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem bit_forall {I : Type*} [Fintype I] (p : I → Prop) :
    bit (∀ i, p i) = ∏ i, bit (p i) := by
  by_cases h : ∀ i, p i
  · simp [bit, h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [show bit (∀ i, p i) = 0 by simp [bit, h]]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [bit, hi])

namespace FiniteProb

variable {I : Type*} [Fintype I] [DecidableEq I]
  {T : I → Type*} [∀ i, Fintype (T i)]

theorem pi_observe_probability (P : ∀ i, FiniteProb (T i))
    (S : Finset I) (x₀ : ∀ i, T i) :
    (pi P).prob (fun x => observeInputs S x = observeInputs S x₀) =
      ∏ i, if i ∈ S then (P i).weight (x₀ i) else 1 := by
  have hb (x : ∀ i, T i) : bit (observeInputs S x = observeInputs S x₀) =
      ∏ i, if i ∈ S then bit (x i = x₀ i) else 1 := by
    rw [show bit (observeInputs S x = observeInputs S x₀) = bit (∀ i, i ∈ S → x i = x₀ i) from
      congrArg bit (propext (observeInputs_eq_iff S x x₀)), bit_forall]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi, bit]
  change (pi P).expect _ = _
  rw [(pi P).expect_congr hb, expect_pi_prod P
    (fun i a => if i ∈ S then bit (a = x₀ i) else 1)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [hi, expect, bit]
  · simp [hi]

def pinInputs (P : ∀ i, FiniteProb (T i)) (S : Finset I) (x₀ : ∀ i, T i) :
    ∀ i, FiniteProb (T i) := fun i => if i ∈ S then pointMass (x₀ i) else P i

theorem given_observe_eq_pi (P : ∀ i, FiniteProb (T i)) (S : Finset I) (x₀ : ∀ i, T i)
    (hb : 0 < ((pi P).map (observeInputs S)).weight (observeInputs S x₀)) :
    (pi P).given (observeInputs S) (observeInputs S x₀) = pi (pinInputs P S x₀) := by
  have hprob : ((pi P).map (observeInputs S)).weight (observeInputs S x₀) =
      ∏ i, if i ∈ S then (P i).weight (x₀ i) else 1 := pi_observe_probability P S x₀
  ext x
  rw [given_weight _ _ _ hb]
  by_cases hx : observeInputs S x = observeInputs S x₀
  · have hfactor : (pi P).weight x =
        ((pi P).map (observeInputs S)).weight (observeInputs S x₀) *
          (pi (pinInputs P S x₀)).weight x := by
      rw [hprob]
      change (∏ i, (P i).weight (x i)) =
        (∏ i, if i ∈ S then (P i).weight (x₀ i) else 1) *
          ∏ i, (pinInputs P S x₀ i).weight (x i)
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · have heq := (observeInputs_eq_iff S x x₀).mp hx i hi
        simp [pinInputs, hi, pointMass, bit, heq]
      · simp [pinInputs, hi]
    rw [hfactor]
    simp [bit, hx, ne_of_gt hb]
  · have hx' : ∃ i, i ∈ S ∧ x i ≠ x₀ i := by
      by_contra hn
      apply hx
      apply (observeInputs_eq_iff S x x₀).mpr
      intro i hi
      by_contra he
      exact hn ⟨i,hi,he⟩
    obtain ⟨i,hi,hxi⟩ := hx'
    have hzero : (pi (pinInputs P S x₀)).weight x = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [pinInputs, hi, pointMass, bit, hxi]
    simp [bit, hx, hzero]

theorem map_positive_has_preimage {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ : FiniteProb Ω) (X : Ω → A) (a : A) (ha : 0 < (μ.map X).weight a) :
    ∃ ω, X ω = a := by
  by_contra hn
  have he : μ.prob (fun ω => X ω = a) = 0 := by
    rw [μ.prob_congr (q := fun _ => False) (by
      intro ω
      exact ⟨fun h => hn ⟨ω,h⟩, False.elim⟩), prob_false]
  change 0 < μ.prob (fun ω => X ω = a) at ha
  linarith

/-- No assertion is made for null fibers, where `given` uses its documented
fallback distribution. All probabilistic uses average with the fiber weight. -/
theorem given_observe_is_product (P : ∀ i, FiniteProb (T i)) (S : Finset I)
    (y : ∀ i, Option (T i)) (hy : 0 < ((pi P).map (observeInputs S)).weight y) :
    ∃ Q : ∀ i, FiniteProb (T i), (pi P).given (observeInputs S) y = pi Q := by
  obtain ⟨x,hx⟩ := (pi P).map_positive_has_preimage (observeInputs S) y hy
  refine ⟨pinInputs P S x, ?_⟩
  rw [← hx]
  exact given_observe_eq_pi P S x (by rwa [hx])

theorem conditional_disjoint_blocks_independent {J : Type*} [Fintype J] [DecidableEq J]
    {B : J → Type*} (P : ∀ i, FiniteProb (T i)) (S : Finset I)
    (y : ∀ i, Option (T i)) (hy : 0 < ((pi P).map (observeInputs S)).weight y)
    (owner : I → Option J) (f : ∀ j, (∀ i : {i // owner i = some j}, T i.val) → B j) :
    ((pi P).given (observeInputs S) y).Independent (fun j x => f j (fun i => x i.val)) := by
  obtain ⟨Q,hQ⟩ := given_observe_is_product P S y hy
  rw [hQ]
  exact disjoint_blocks_independent Q owner f

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/SharedViews.lean ===== -/

/-! Conditional independence from disjoint coordinate dependencies. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def ReadsOnly {I A : Type*} {T : I → Type*} (Y : (∀ i, T i) → A) (S : Finset I) : Prop :=
  ∀ x z, (∀ i ∈ S, x i = z i) → Y x = Y z

theorem ReadsOnly.doesNotRead {I A : Type*} {T : I → Type*}
    {Y : (∀ i, T i) → A} {S : Finset I} (h : ReadsOnly Y S) (i : I) (hi : i ∉ S) :
    FiniteProb.DoesNotRead Y i := by
  intro x z hxz
  apply h
  intro j hj
  exact hxz j (fun hji => hi (hji ▸ hj))

namespace FiniteProb

theorem Independent.congr_on_support {Ω J : Type*} [Fintype Ω] [Fintype J]
    {B : J → Type*} {μ : FiniteProb Ω} {X Y : ∀ j, Ω → B j}
    (h : μ.Independent X) (hXY : ∀ j ω, 0 < μ.weight ω → X j ω = Y j ω) : μ.Independent Y := by
  intro f
  calc
    _ = μ.expect (fun ω => ∏ j, f j (X j ω)) := by
      apply μ.expect_congr_on_support
      intro ω hω
      exact Finset.prod_congr rfl (fun j _ => congrArg (f j) (hXY j ω hω).symm)
    _ = ∏ j, μ.expect (fun ω => f j (X j ω)) := h f
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      apply μ.expect_congr_on_support
      intro ω hω
      exact congrArg (f j) (hXY j ω hω)

/-- Variables may share arbitrary observed coordinates. Outside the observed
set their read sets must be pairwise disjoint. Conditional independence then
follows from the actual product input distribution. -/
theorem conditional_independent_of_disjoint_reads
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {T : I → Type*} [∀ i, Fintype (T i)] {B : J → Type*}
    (P : ∀ i, FiniteProb (T i)) (Y : ∀ j, (∀ i, T i) → B j)
    (reads : J → Finset I) (S : Finset I)
    (hlocal : ∀ j, ReadsOnly (Y j) (reads j))
    (hdisjoint : ∀ j k, j ≠ k → ∀ i, i ∈ reads j → i ∈ reads k → i ∈ S)
    (y : ∀ i, Option (T i)) (hy : 0 < ((pi P).map (observeInputs S)).weight y) :
    ((pi P).given (observeInputs S) y).Independent Y := by
  obtain ⟨x₀,hx₀⟩ := (pi P).map_positive_has_preimage (observeInputs S) y hy
  let owner : I → Option J := fun i =>
    if h : ∃ j, i ∈ reads j ∧ i ∉ S then some h.choose else none
  have howner (j : J) (i : I) (hi : i ∈ reads j) (hiS : i ∉ S) : owner i = some j := by
    have hex : ∃ k, i ∈ reads k ∧ i ∉ S := ⟨j,hi,hiS⟩
    have heq : hex.choose = j := by
      by_contra hn
      exact hiS (hdisjoint hex.choose j hn i hex.choose_spec.1 hi)
    simp [owner, hex, heq]
  let f : ∀ j, (∀ i : {i // owner i = some j}, T i.val) → B j :=
    fun j z => Y j (fun i => if h : owner i = some j then z ⟨i,h⟩ else x₀ i)
  have hblock := conditional_disjoint_blocks_independent P S y hy owner f
  apply hblock.congr_on_support
  intro j x hx
  symm
  apply hlocal j
  intro i hi
  have hxy : observeInputs S x = observeInputs S x₀ :=
    ((pi P).given_support_eq (observeInputs S) y hy hx).trans hx₀.symm
  by_cases hiS : i ∈ S
  · have hv := (observeInputs_eq_iff S x x₀).mp hxy i hiS
    dsimp
    split_ifs <;> simp_all
  · have ho := howner j i hi hiS
    dsimp
    simp only [ho, dite_true, if_true]

theorem independent_bool_pair_distribution {Ω A : Type*} [Fintype Ω] [Fintype A]
    (μ : FiniteProb Ω) (Y : Bool → Ω → A) (h : μ.Independent Y) :
    μ.map (fun ω => (Y false ω,Y true ω)) = (μ.map (Y false)).product (μ.map (Y true)) := by
  ext ab
  have hf := h (fun b a => bit (a = if b then ab.2 else ab.1))
  simp only [Fintype.prod_bool, Bool.false_eq_true, if_false, if_true] at hf
  change μ.expect (fun ω => bit ((Y false ω,Y true ω) = ab)) =
    μ.expect (fun ω => bit (Y false ω = ab.1)) * μ.expect (fun ω => bit (Y true ω = ab.2))
  have he (ω : Ω) : bit ((Y false ω,Y true ω) = ab) =
      bit (Y false ω = ab.1)*bit (Y true ω = ab.2) := by
    by_cases h0 : Y false ω = ab.1 <;> by_cases h1 : Y true ω = ab.2 <;>
      simp [bit, Prod.ext_iff, h0, h1]
  rw [μ.expect_congr he]
  simpa only [mul_comm] using hf

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/NestedGiven.lean ===== -/

/-! Exact successive conditioning, with positivity rather than conventions
about zero-probability fibers doing the cancellation. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem given_positive_original (μ : FiniteProb Ω) (Y : Ω → B) (b : B)
    (hb : 0 < (μ.map Y).weight b) {ω : Ω} (hω : 0 < (μ.given Y b).weight ω) :
    0 < μ.weight ω := by
  rw [μ.given_weight Y b hb] at hω
  have hy := μ.given_support_eq Y b hb
    (show 0 < (μ.given Y b).weight ω by rwa [μ.given_weight Y b hb])
  simp only [hy, bit, if_true, mul_one] at hω
  exact (div_pos_iff_of_pos_right hb).mp hω

theorem given_refinement_mass (μ : FiniteProb Ω) (F : Ω → A) (Y : Ω → B)
    (coarse : A → B) (hY : ∀ ω, Y ω = coarse (F ω)) (a : A)
    (hb : 0 < (μ.map Y).weight (coarse a)) :
    ((μ.given Y (coarse a)).map F).weight a =
      (μ.map F).weight a / (μ.map Y).weight (coarse a) := by
  rw [μ.given_pair_mass F Y a (coarse a) hb]
  congr 1
  apply μ.prob_congr
  intro ω
  simp only [Prod.mk.injEq, hY]
  exact ⟨And.left, fun h => ⟨h,congrArg coarse h⟩⟩

theorem given_given_refinement (μ : FiniteProb Ω) (F : Ω → A) (Y : Ω → B)
    (coarse : A → B) (hY : ∀ ω, Y ω = coarse (F ω)) (a : A)
    (ha : 0 < (μ.map F).weight a) :
    (μ.given Y (coarse a)).given F a = μ.given F a := by
  have hb : 0 < (μ.map Y).weight (coarse a) := lt_of_lt_of_le ha
    (μ.prob_mono (fun ω h => (hY ω).trans (congrArg coarse h)))
  have hm := μ.given_refinement_mass F Y coarse hY a hb
  have hp : 0 < ((μ.given Y (coarse a)).map F).weight a := by rw [hm]; positivity
  ext ω
  rw [given_weight _ F a hp, μ.given_weight Y (coarse a) hb, hm, μ.given_weight F a ha]
  by_cases hf : F ω = a
  · have hy : Y ω = coarse a := (hY ω).trans (congrArg coarse hf)
    simp only [hf, hy, bit, if_true, mul_one]
    field_simp
  · simp [bit, hf]

theorem given_given_at_support (μ : FiniteProb Ω) (F : Ω → A) (Y : Ω → B)
    (coarse : A → B) (hY : ∀ ω, Y ω = coarse (F ω)) (b : B)
    (hb : 0 < (μ.map Y).weight b) {ω : Ω} (hω : 0 < (μ.given Y b).weight ω) :
    (μ.given Y b).given F (F ω) = μ.given F (F ω) := by
  have hy := μ.given_support_eq Y b hb hω
  have ha := μ.map_weight_pos F (μ.given_positive_original Y b hb hω)
  have h := μ.given_given_refinement F Y coarse hY (F ω) ha
  rwa [← hY ω, hy] at h

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/WeightedBranch.lean ===== -/

/-! The relative branch estimate, averaged with the local occupancy weight.
This weighted form is essential: an unweighted error would lose the desired
linear dependence on the occupied mass. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C I : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype I]

def occupancyScalar (μ : FiniteProb Ω) (U : Ω → Option A) (Y : Ω → B) (D : ℝ) (b : B) : ℝ :=
  max ((μ.given Y b).prob (fun ω => U ω ≠ none)-2/D) 0 / 2

omit [Fintype A] in
theorem occupancyScalar_nonneg (μ : FiniteProb Ω) (U : Ω → Option A) (Y : Ω → B)
    (D : ℝ) (b : B) : 0 ≤ μ.occupancyScalar U Y D b := by
  exact div_nonneg (le_max_right _ _) (by norm_num)

omit [Fintype A] in
theorem occupancyScalar_le_one (μ : FiniteProb Ω) (U : Ω → Option A) (Y : Ω → B)
    {D : ℝ} (hD : 0 < D) (b : B) : μ.occupancyScalar U Y D b ≤ 1 := by
  have h := (μ.given Y b).prob_le_one (fun ω => U ω ≠ none)
  have hi : 0 < 2/D := div_pos (by norm_num) hD
  unfold occupancyScalar
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  exact max_le (by linarith) (by norm_num)

omit [Fintype A] in
theorem occupancyScalar_mass (μ : FiniteProb Ω) (U : Ω → Option A) (Y : Ω → B) (D : ℝ) :
    μ.prob (fun ω => U ω ≠ none) ≤
      2*μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω))+2/D := by
  have h := (μ.map Y).expect_mono (fun b =>
    show (μ.given Y b).prob (fun ω => U ω ≠ none) ≤ 2*μ.occupancyScalar U Y D b+2/D by
      have h := le_max_left ((μ.given Y b).prob (fun ω => U ω ≠ none)-2/D) 0
      dsimp [occupancyScalar]
      linarith)
  rw [expect_add, expect_mul, expect_const] at h
  have ht := μ.total_conditional_expectation Y (fun ω => bit (U ω ≠ none))
  change (μ.map Y).expect (fun b => (μ.given Y b).prob (fun ω => U ω ≠ none)) =
    μ.prob (fun ω => U ω ≠ none) at ht
  rwa [ht, expect_map] at h

/-- Conditional probability of too-small shared-view tails, in a fixed
positive inner-view fiber. The finer conditioning is proved to agree with
successive conditioning; it is not an extra independence assumption. -/
theorem relative_branch_failures (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : Ω → B) (F : I → Ω → C) (coarse : I → C → B)
    (href : ∀ i ω, Y ω = coarse i (F i ω)) (ell M m : ℕ)
    (hD : 12 ≤ (Fintype.card I : ℝ)) (hlog : 1 ≤ Real.log (Fintype.card I : ℝ))
    (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*Fintype.card I ≤ (Fintype.card I : ℝ)^4)
    (hratio : (M:ℝ)/m = 1/(Fintype.card I : ℝ))
    (b : B) (hb : 0 < (μ.map Y).weight b)
    (hind : (μ.given Y b).Independent F)
    (hatom : ∀ a, ((μ.given Y b).map U).weight (some a) ≤ 1/(m:ℝ))
    (hf : 0 < μ.occupancyScalar U Y (Fintype.card I) b) :
    (∑ i, (μ.given Y b).prob (fun ω =>
      ((μ.given (F i) (F i ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) b)) ≤
      256*Real.log (Fintype.card I : ℝ) := by
  let D : ℝ := Fintype.card I
  have hDp : 0 < D := by dsimp [D]; linarith
  have hlo := (((μ.given Y b).map U)).tail_lower_of_atom_bound M
    (show (0:ℝ) ≤ 1/(m:ℝ) by positivity) hatom
  rw [prob_map, mul_one_div, hratio] at hlo
  have hscalar : μ.occupancyScalar U Y D b =
      ((μ.given Y b).prob (fun ω => U ω ≠ none)-2/D)/2 := by
    unfold occupancyScalar at hf ⊢
    rw [max_eq_left]
    by_contra h
    rw [max_eq_right (le_of_not_ge h)] at hf
    norm_num at hf
  have hp : 2/D < (μ.given Y b).prob (fun ω => U ω ≠ none) := by
    change 0 < μ.occupancyScalar U Y D b at hf
    rw [hscalar] at hf
    linarith
  have ht : 1/D ≤ ((μ.given Y b).map U).tail M := by
    change _ - 1/D ≤ _ at hlo
    simp only [div_eq_mul_inv] at hp hlo ⊢
    linarith
  have hft : μ.occupancyScalar U Y D b ≤ ((μ.given Y b).map U).tail M/2 := by
    rw [hscalar]
    change _ - 1/D ≤ _ at hlo
    have hi : 0 < 1/D := one_div_pos.mpr hDp
    simp only [div_eq_mul_inv] at hlo hi ⊢
    linarith
  have hbranch := (μ.given Y b).branch_transfer F U hind ell M hD hlog hM hellM hsize ht
  apply le_trans _ hbranch
  apply Finset.sum_le_sum
  intro i _
  apply (μ.given Y b).expect_mono_on_support
  intro ω hω
  have he := μ.given_given_at_support (F i) Y (coarse i) (href i) b hb hω
  dsimp only
  rw [he]
  exact bit_mono (fun h => lt_of_lt_of_le h hft)

theorem weighted_branch_failures (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : Ω → B) (F : I → Ω → C) (coarse : I → C → B)
    (href : ∀ i ω, Y ω = coarse i (F i ω)) (ell M m : ℕ)
    (hD : 12 ≤ (Fintype.card I : ℝ)) (hlog : 1 ≤ Real.log (Fintype.card I : ℝ))
    (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*Fintype.card I ≤ (Fintype.card I : ℝ)^4)
    (hratio : (M:ℝ)/m = 1/(Fintype.card I : ℝ))
    (hind : ∀ b, 0 < (μ.map Y).weight b → (μ.given Y b).Independent F)
    (hatom : ∀ b, 0 < (μ.map Y).weight b → ∀ a,
      ((μ.given Y b).map U).weight (some a) ≤ 1/(m:ℝ)) :
    (∑ i, μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω) *
      bit (((μ.given (F i) (F i ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) (Y ω)))) ≤
      256*Real.log (Fintype.card I : ℝ) *
        μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω)) := by
  let f := μ.occupancyScalar U Y (Fintype.card I)
  let fail := fun i ω => ((μ.given (F i) (F i ω)).map U).tail ell < f (Y ω)
  have hpoint (b : B) (hb : 0 < (μ.map Y).weight b) :
      (μ.given Y b).expect (fun ω => ∑ i, f (Y ω)*bit (fail i ω)) ≤
        256*Real.log (Fintype.card I : ℝ)*f b := by
    rw [expect_sum]
    have he (i : I) : (μ.given Y b).expect (fun ω => f (Y ω)*bit (fail i ω)) =
        f b * (μ.given Y b).prob (fun ω => ((μ.given (F i) (F i ω)).map U).tail ell < f b) := by
      rw [μ.given_pullout Y b hb f]
      congr 1
      exact μ.given_prob_congr Y b hb _ _ (by intro ω hω; simp only [fail, hω])
    simp only [he, ← Finset.mul_sum]
    by_cases hf : 0 < f b
    · have h := μ.relative_branch_failures U Y F coarse href ell M m hD hlog hM hm
        hellM hsize hratio b hb (hind b hb) (hatom b hb) hf
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left h hf.le
    · have hz : f b = 0 := le_antisymm (le_of_not_gt hf) (μ.occupancyScalar_nonneg U Y _ b)
      simp [hz]
  have hav := (μ.map Y).expect_mono_on_support _ _ hpoint
  rw [expect_mul] at hav
  have ht := μ.total_conditional_expectation Y (fun ω => ∑ i, f (Y ω)*bit (fail i ω))
  change (μ.map Y).expect (fun b => (μ.given Y b).expect
    (fun ω => ∑ i, f (Y ω)*bit (fail i ω))) = _ at ht
  rw [ht, expect_sum, expect_map] at hav
  exact hav

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/EndpointTails.lean ===== -/

/-! Averaging the dense-matrix estimate on genuine conditional fibers. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

theorem product_selected_probability (P : FiniteProb (Option A))
    (Q : FiniteProb (Option B)) (G : A → B → Prop) :
    (P.product Q).prob (fun ab => selectedConflict (fun _ : Unit => G) ((),ab.1,ab.2)) =
      ∑ a, ∑ b, P.weight (some a) * Q.weight (some b) * bit (G a b) := by
  simp only [prob, expect, product, Fintype.sum_prod_type, Fintype.sum_option, selectedConflict,
    bit_false, mul_zero, Finset.sum_const_zero, zero_add]

theorem matrix_tail_product [DecidableEq A] (P Q : FiniteProb (Option A))
    (G : A × A → Bool) {ell : ℕ} (hell : 0 < ell) :
    P.tail ell * Q.tail ell ≤
      4*(P.product Q).prob (fun ab => selectedConflict (fun _ : Unit => fun a b => G (a,b) = true)
        ((),ab.1,ab.2)) + bit (exceptionalMatrix ell G) := by
  by_cases hbad : exceptionalMatrix ell G
  · rw [show bit (exceptionalMatrix ell G) = 1 by simp [bit, hbad]]
    have hp := P.listTail_le_one (P.outputList ell)
    have hq := Q.listTail_le_one (Q.outputList ell)
    have hq0 := Q.listTail_nonneg (Q.outputList ell)
    have hm := mul_le_mul hp hq hq0 (by norm_num : (0:ℝ) ≤ 1)
    have he := (P.product Q).prob_nonneg
      (fun ab => selectedConflict (fun _ : Unit => fun a b => G (a,b) = true) ((),ab.1,ab.2))
    change P.tail ell*Q.tail ell ≤ 1*1 at hm
    linarith
  · rw [show bit (exceptionalMatrix ell G) = 0 by simp [bit, hbad], add_zero,
      product_selected_probability]
    apply dense_boolean_tail_product P Q (fun a b => G (a,b) = true) hell
    intro S hS T hT
    have hd : ¬ rectangleCount S T G ≤ (ell : ℝ)^2/4 :=
      fun h => hbad ⟨⟨S,hS⟩,⟨T,hT⟩,h⟩
    exact (lt_of_not_ge hd).le

/-- Endpoint outputs may depend on the central matrix. The only required
independence is their conditional independence given the shared view `F`.
Null fibers are handled by zero weights rather than assumed absent. -/
theorem conditional_endpoint_tails [DecidableEq A] (μ : FiniteProb Ω)
    (U V : Ω → Option A) (F : Ω → C) (G : C → A × A → Bool)
    {ell : ℕ} (hell : 0 < ell) {q : ℝ}
    (hind : ∀ b, 0 < (μ.map F).weight b →
      (μ.given F b).map (fun ω => (U ω,V ω)) =
        ((μ.given F b).map U).product ((μ.given F b).map V))
    (hbad : μ.prob (fun ω => exceptionalMatrix ell (G (F ω))) ≤ q) :
    μ.expect (fun ω => ((μ.given F (F ω)).map U).tail ell *
      ((μ.given F (F ω)).map V).tail ell) ≤
      4*μ.prob (fun ω => selectedConflict (fun b a a' => G b (a,a') = true) (F ω,U ω,V ω)) + q := by
  let conflict := fun ω => selectedConflict (fun b a a' => G b (a,a') = true) (F ω,U ω,V ω)
  have hpoint (b : C) (hb : 0 < (μ.map F).weight b) :
      ((μ.given F b).map U).tail ell*((μ.given F b).map V).tail ell ≤
        4*(μ.given F b).prob conflict + bit (exceptionalMatrix ell (G b)) := by
    have he := matrix_tail_product ((μ.given F b).map U) ((μ.given F b).map V) (G b) hell
    rw [← hind b hb, prob_map] at he
    have hc : (μ.given F b).prob conflict =
        (μ.given F b).prob (fun ω => selectedConflict (fun _ : Unit => fun a a' => G b (a,a') = true)
          ((),U ω,V ω)) := by
      apply μ.given_prob_congr F b hb
      intro ω hω
      simp only [conflict, hω, selectedConflict]
    rwa [hc]
  have hmean : (μ.map F).expect (fun b => (μ.given F b).prob conflict) = μ.prob conflict :=
    μ.total_conditional_expectation F (fun ω => bit (conflict ω))
  have hsum := (μ.map F).expect_mono_on_support _ _ hpoint
  rw [expect_add, expect_mul, hmean] at hsum
  change (μ.map F).expect (fun b => ((μ.given F b).map U).tail ell*((μ.given F b).map V).tail ell) ≤
    4*μ.prob conflict + (μ.map F).prob (fun b => exceptionalMatrix ell (G b)) at hsum
  rw [expect_map, prob_map] at hsum
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/ListParameters.lean ===== -/

/-! One explicit degree threshold for all list and matrix parameters. -/

namespace MISLocal
noncomputable section

def listEll (k : ℕ) : ℕ := ⌈100*Real.log ((k:ℝ)+1)⌉₊
def listMiddle (k : ℕ) : ℕ := 1000*listEll k
def listCapacity (D k : ℕ) : ℕ := D*listMiddle k

theorem log_add_one_le {k : ℝ} (hk : 1 ≤ k) : Real.log (k+1) ≤ Real.log k+1 := by
  have hkp : 0 < k := by linarith
  have h := Real.log_le_log (show 0 < k+1 by linarith) (show k+1 ≤ 2*k by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hkp)] at h
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

theorem listEll_bounds {D : ℝ} {k : ℕ} (hk : 1 ≤ k) (hD : 1 ≤ D)
    (hlower : D ≤ Real.log (k:ℝ)) (hupper : Real.log (k:ℝ) ≤ D^2) :
    100*Real.log (k:ℝ) ≤ (listEll k : ℝ) ∧ (listEll k : ℝ) ≤ 100*D^2+101 := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith
  have hlo := Real.log_le_log hkp (show (k:ℝ) ≤ k+1 by linarith)
  have hceil := Nat.le_ceil (100*Real.log ((k:ℝ)+1))
  have hx : 0 ≤ 100*Real.log ((k:ℝ)+1) := by linarith
  have hceil' := Nat.ceil_lt_add_one hx
  have hlog := log_add_one_le hk'
  change _ ≤ (listEll k : ℝ) at hceil
  change (listEll k : ℝ) < _ at hceil'
  constructor <;> linarith

theorem explicit_list_parameters {D k : ℕ} (hD : 1048576 ≤ D) (hk : 1 ≤ k)
    (hlower : (D:ℝ) ≤ Real.log (k:ℝ)) (hupper : Real.log (k:ℝ) ≤ (D:ℝ)^2) :
    0 < listEll k ∧ 0 < listMiddle k ∧ 0 < listCapacity D k ∧
      32*listEll k ≤ listMiddle k ∧
      (listCapacity D k : ℝ) ≤ (D:ℝ)^4 ∧
      (listMiddle k : ℝ)/(listCapacity D k : ℝ) = 1/(D:ℝ) ∧
      1 ≤ Real.log (D:ℝ) := by
  have hDr : (1048576:ℝ) ≤ D := by exact_mod_cast hD
  have hDp : (0:ℝ) < D := by linarith
  obtain ⟨hell,hell'⟩ := listEll_bounds hk (show (1:ℝ) ≤ D by linarith) hlower hupper
  have hellp : 0 < listEll k := by
    have h : (0:ℝ) < listEll k := by linarith
    exact_mod_cast h
  have hMp : 0 < listMiddle k := Nat.mul_pos (by decide) hellp
  have hDn : 0 < D := by omega
  have hmp : 0 < listCapacity D k := Nat.mul_pos hDn hMp
  have hMu : (listMiddle k : ℝ) ≤ (D:ℝ)^3 := by
    have hm : (listMiddle k : ℝ) ≤ 100000*(D:ℝ)^2+101000 := by
      dsimp [listMiddle]
      push_cast
      linarith
    have hc := mul_le_mul_of_nonneg_right hDr (sq_nonneg (D:ℝ))
    nlinarith [sq_nonneg ((D:ℝ)-1)]
  refine ⟨hellp,hMp,hmp,by dsimp [listMiddle]; omega,?_,?_,?_⟩
  · change ((D*listMiddle k : ℕ):ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      _ ≤ (D:ℝ)*(D:ℝ)^3 := mul_le_mul_of_nonneg_left hMu hDp.le
      _ = _ := by ring
  · have hMne : (listMiddle k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hMp)
    simp only [listCapacity, Nat.cast_mul]
    field_simp
    ring
  · have he := Real.abs_exp_sub_one_le (x := (1:ℝ)) (by norm_num)
    have h3 : Real.exp (1:ℝ) ≤ 3 := by
      have hh := (le_abs_self (Real.exp (1:ℝ)-1)).trans he
      norm_num at hh
      linarith
    have hl := Real.log_le_log (Real.exp_pos (1:ℝ)) (show Real.exp (1:ℝ) ≤ D by linarith)
    simpa using hl

theorem matrix_numeric_bound {D k : ℝ} {ell : ℕ} (hD : 12 ≤ D) (hk : 0 < k)
    (hlower : D ≤ Real.log k) (hell : 100*Real.log k ≤ (ell:ℝ)) :
    k^(2*ell)*Real.exp (-(ell:ℝ)^2/16) ≤ 1/D^2 := by
  have hDp : 0 < D := by linarith
  have hl0 : 0 ≤ Real.log k := by linarith
  have he0 : (0:ℝ) ≤ ell := Nat.cast_nonneg _
  have h64 : 64*Real.log k ≤ (ell:ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_left h64 he0
  have hlogD := Real.log_le_sub_one_of_pos hDp
  have hellsq : 64*Real.log D ≤ (ell:ℝ)^2 := by
    nlinarith [sq_nonneg ((ell:ℝ)-1)]
  calc
    _ = Real.exp ((2*(ell:ℝ))*Real.log k-(ell:ℝ)^2/16) := by
      rw [Real.exp_sub, show Real.exp ((2*(ell:ℝ))*Real.log k) = k^(2*ell) by
        norm_cast; rw [Real.exp_nat_mul, Real.exp_log hk]]
      rw [show -(ell:ℝ)^2/16 = -((ell:ℝ)^2/16) by ring, Real.exp_neg]
      ring
    _ ≤ Real.exp (-(ell:ℝ)^2/32) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ Real.exp (-(2:ℝ)*Real.log D) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := exp_neg_nat_log hDp 2

end
end MISLocal


/- ===== Source: MISLocal/TableSampling.lean ===== -/

/-! A finite stochastic rule is realized by a private table, independently
sampled at every vertex. Tables are indexed by the LOCAL view, not the entire
input configuration; this distinction preserves pointwise locality. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C I : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
  [Fintype I] [DecidableEq I] [DecidableEq B]

theorem pi_expect_two {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (i j : I) (hji : j ≠ i)
    (f : T i → ℝ) (g : T j → ℝ) :
    (pi P).expect (fun x => f (x i)*g (x j)) = (P i).expect f * (P j).expect g := by
  have he := (pi P).expect_map (Equiv.piSplitAt i T)
    (fun ab => f ab.1*g (ab.2 ⟨j,hji⟩))
  rw [pi_splitAt, product_expect] at he
  simp only [expect_mul, pi_expect_coordinate, Equiv.piSplitAt_apply] at he
  rw [← he]
  simp only [expect, ← mul_assoc, ← Finset.sum_mul]

def tableProbability (K : I → B → FiniteProb A) : FiniteProb (I → B → A) :=
  pi (fun i => pi (K i))

def tableDraw (Y : I → Ω → B) (i : I) (x : Ω × (I → B → A)) : A := x.2 i (Y i x.1)

theorem table_expect_one (K : I → B → FiniteProb A) (i : I) (b : B) (f : A → ℝ) :
    (tableProbability K).expect (fun t => f (t i b)) = (K i b).expect f := by
  exact (pi_expect_coordinate (fun i => pi (K i)) i (fun t => f (t b))).trans
    (pi_expect_coordinate (K i) b f)

theorem table_expect_pair (K : I → B → FiniteProb A) (i j : I) (hji : j ≠ i)
    (b c : B) (f g : A → ℝ) :
    (tableProbability K).expect (fun t => f (t i b)*g (t j c)) =
      (K i b).expect f * (K j c).expect g := by
  rw [tableProbability, pi_expect_two (fun i => pi (K i)) i j hji
    (fun t => f (t b)) (fun t => g (t c))]
  rw [pi_expect_coordinate, pi_expect_coordinate]

theorem table_pair_distribution (K : I → B → FiniteProb A) (i j : I) (hji : j ≠ i)
    (b c : B) :
    (tableProbability K).map (fun t => (t i b,t j c)) = (K i b).product (K j c) := by
  ext ab
  change (tableProbability K).expect (fun t => bit ((t i b,t j c) = ab)) = _
  have he (t : I → B → A) : bit ((t i b,t j c) = ab) =
      bit (t i b = ab.1)*bit (t j c = ab.2) := by
    by_cases h0 : t i b = ab.1 <;> by_cases h1 : t j c = ab.2 <;>
      simp [bit, Prod.ext_iff, h0, h1]
  rw [(tableProbability K).expect_congr he,
    table_expect_pair K i j hji b c (fun x => bit (x = ab.1)) (fun x => bit (x = ab.2))]
  simp [expect, bit, product]

omit [DecidableEq B] in
theorem product_map_left (P : FiniteProb Ω) (Q : FiniteProb A) (Y : Ω → B) :
    (P.product Q).map (fun x => Y x.1) = P.map Y := by
  rw [← map_comp _ Prod.fst Y, product_map_fst]

omit [DecidableEq B] in
theorem product_given_left (P : FiniteProb Ω) (Q : FiniteProb A) (Y : Ω → B)
    (b : B) (hb : 0 < (P.map Y).weight b) :
    (P.product Q).given (fun x => Y x.1) b = (P.given Y b).product Q := by
  have hb' : 0 < ((P.product Q).map (fun x => Y x.1)).weight b := by
    rwa [product_map_left]
  ext x
  rw [given_weight _ _ b hb', product_map_left]
  change (P.weight x.1*Q.weight x.2)*bit (Y x.1=b)/(P.map Y).weight b =
    (P.given Y b).weight x.1*Q.weight x.2
  rw [P.given_weight Y b hb]
  ring

/-- Sampling the original output's conditional distribution reproduces
that distribution exactly on every positive local-view fiber. -/
theorem sampled_conditional_output (μ : FiniteProb Ω) (U : I → Ω → A) (Y : I → Ω → B)
    (i : I) (b : B) (hb : 0 < (μ.map (Y i)).weight b) :
    let K := fun i b => (μ.given (Y i) b).map (U i)
    ((μ.product (tableProbability K)).given (fun x => Y i x.1) b).map (tableDraw Y i) = K i b := by
  dsimp only
  rw [product_given_left μ _ (Y i) b hb]
  ext a
  change ((μ.given (Y i) b).product _).expect (fun x => bit (tableDraw Y i x = a)) = _
  rw [product_expect]
  simp only [tableDraw]
  simp_rw [table_expect_one _ i _ (fun x => bit (x = a))]
  calc
    _ = (μ.given (Y i) b).expect (fun _ => ((μ.given (Y i) b).map (U i)).weight a) := by
      apply (μ.given (Y i) b).expect_congr_on_support
      intro ω hω
      dsimp only
      rw [μ.given_support_eq (Y i) b hb hω]
      simp [expect, bit]
    _ = _ := expect_const _ _

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/AnySourceEntropy.lean ===== -/

/-! The revelation proof for an arbitrary finite index type, including sums
of edge sources and vertex-private tables. Enumeration affects only the proof,
not the probability space or the rule. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def sourcePrefix (I : Type*) [Fintype I] [DecidableEq I] (t : ℕ) : Finset I :=
  Finset.univ.filter (fun i => (Fintype.equivFin I i).val < t)

@[simp] theorem sourcePrefix_zero (I : Type*) [Fintype I] [DecidableEq I] :
    sourcePrefix I 0 = ∅ := by ext i; simp [sourcePrefix]

@[simp] theorem sourcePrefix_full (I : Type*) [Fintype I] [DecidableEq I] :
    sourcePrefix I (Fintype.card I) = Finset.univ := by
  ext i
  simp [sourcePrefix, (Fintype.equivFin I i).isLt]

theorem sourcePrefix_succ (I : Type*) [Fintype I] [DecidableEq I]
    (i : Fin (Fintype.card I)) :
    sourcePrefix I (i.val+1) = insert ((Fintype.equivFin I).symm i) (sourcePrefix I i.val) := by
  ext j
  simp only [sourcePrefix, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [← (Fintype.equivFin I).apply_eq_iff_eq_symm_apply, Fin.ext_iff]
  omega

theorem source_not_prefix (I : Type*) [Fintype I] [DecidableEq I]
    (i : Fin (Fintype.card I)) : (Fintype.equivFin I).symm i ∉ sourcePrefix I i.val := by
  simp [sourcePrefix]

namespace FiniteProb

theorem revealGain_sum_finite {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] {A : Type*} [Fintype A]
    (P : ∀ i, FiniteProb (T i)) (Y : (∀ i, T i) → A) (S : Finset I) :
    (∑ i : Fin (Fintype.card I), revealGain P Y (S ∪ sourcePrefix I i.val)
      ((Fintype.equivFin I).symm i)) = (pi P).condEntropy Y (observeInputs S) := by
  let f : ℕ → ℝ := fun t => (pi P).condEntropy Y (observeInputs (S ∪ sourcePrefix I t))
  have he (i : Fin (Fintype.card I)) : revealGain P Y (S ∪ sourcePrefix I i.val)
      ((Fintype.equivFin I).symm i) = f i.val-f (i.val+1) := by
    simp only [revealGain, f, sourcePrefix_succ, Finset.union_insert]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun t => f t-f (t+1)) (Fintype.card I), Finset.sum_range_sub']
  have hfull : f (Fintype.card I) = 0 := by
    change (pi P).condEntropy Y (observeInputs (S ∪ sourcePrefix I (Fintype.card I))) = 0
    rw [sourcePrefix_full, Finset.union_eq_right.mpr (Finset.subset_univ S)]
    apply (pi P).condEntropy_of_determined
    intro x y hxy
    exact congrArg Y (funext (fun i => (observeInputs_eq_iff Finset.univ x y).mp hxy i
      (Finset.mem_univ i)))
  rw [hfull, sub_zero]
  simp [f]

theorem conditional_edge_vertex_entropy_finite {I V E A : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Fintype E] [Fintype A]
    {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (Y : V → (∀ i, T i) → A)
    (left right : E → V) (reads vertexView : V → Finset I) (edgeView : E → Finset I) {d : ℕ}
    (hlocal : ∀ v, ReadsOnly (Y v) (reads v))
    (charge : SourceCharge left right reads vertexView edgeView d) :
    (d : ℝ)*(∑ v, (pi P).condEntropy (Y v) (observeInputs (vertexView v))) ≤
      ∑ e, (pi P).condEntropy (fun x => (Y (left e) x,Y (right e) x))
        (observeInputs (edgeView e)) := by
  have hstep (j : Fin (Fintype.card I)) :
      (d : ℝ)*(∑ v, revealGain P (Y v) (vertexView v ∪ sourcePrefix I j.val)
        ((Fintype.equivFin I).symm j)) ≤
        ∑ e, revealGain P (fun x => (Y (left e) x,Y (right e) x))
          (edgeView e ∪ sourcePrefix I j.val) ((Fintype.equivFin I).symm j) := by
    let i := (Fintype.equivFin I).symm j
    apply sum_le_of_charging (fun v => i ∈ reads v ∧ i ∉ vertexView v) d (charge.route i)
    · intro v hv
      by_cases hi : i ∈ vertexView v
      · exact revealGain_known P (Y v) _ i (Finset.mem_union_left _ hi)
      · exact revealGain_unread P (Y v) _ i
          ((hlocal v).doesNotRead i (fun h => hv ⟨h,hi⟩))
    · intro e
      exact revealGain_nonneg P _ _ i
    · intro z
      apply revealGain_refinement P _ _ _ _ i
      · exact Finset.union_subset_union (charge.contains i z) (Finset.Subset.refl _)
      · exact fun h => (Finset.mem_union.mp h).elim (charge.fresh i z) (source_not_prefix I j)
      · intro x y hxy
        rcases charge.incident i z with hleft | hright
        · simpa only [hleft] using congrArg Prod.fst hxy
        · simpa only [hright] using congrArg Prod.snd hxy
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hstep j)
  rw [← Finset.mul_sum, Finset.sum_comm] at hs
  conv_rhs at hs => rw [Finset.sum_comm]
  simpa only [revealGain_sum_finite] using hs

theorem symmetric_conditional_entropy_finite {I V E A : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Nonempty V] [Fintype E] [Fintype A]
    {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (Y : V → (∀ i, T i) → A)
    (left right : E → V) (reads vertexView : V → Finset I) (edgeView : E → Finset I) {d : ℕ}
    (hlocal : ∀ v, ReadsOnly (Y v) (reads v))
    (charge : SourceCharge left right reads vertexView edgeView d)
    (hcard : 2*Fintype.card E = (d+1)*Fintype.card V) {Hv He : ℝ}
    (hv : ∀ v, (pi P).condEntropy (Y v) (observeInputs (vertexView v)) = Hv)
    (he : ∀ e, (pi P).condEntropy (fun x => (Y (left e) x,Y (right e) x))
      (observeInputs (edgeView e)) = He) :
    ((d : ℝ)+1)/2*He ≥ (d : ℝ)*Hv := by
  have h := conditional_edge_vertex_entropy_finite P Y left right reads vertexView edgeView hlocal charge
  simp only [hv, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hc : (Fintype.card E : ℝ) = ((d : ℝ)+1)*(Fintype.card V : ℝ)/2 := by
    have hc' : (2:ℝ)*Fintype.card E = ((d : ℝ)+1)*Fintype.card V := by exact_mod_cast hcard
    linarith
  rw [hc] at h
  have hp : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_left hp).mp
  convert h using 1 <;> ring

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/PrivateSources.lean ===== -/

/-! Adding genuinely independent vertex-private random sources preserves
the source-routing geometry. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
universe u

def rawView {I V : Type*} (S : Finset I) : Finset (I ⊕ V) := S.map Function.Embedding.inl

def privateReads {I V : Type*} [DecidableEq I] [DecidableEq V]
    (reads : V → Finset I) (v : V) : Finset (I ⊕ V) := rawView (reads v) ∪ {Sum.inr v}

def incidentSelection {V E : Type*} [Fintype E] [DecidableEq E]
    (left right : E → V) (d : ℕ)
    (hdegree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1)
    (v : V) : Fin d ↪ E := by
  let e : Fin (d+1) ≃ {e // e ∈ Finset.univ.filter (edgeIncident left right v)} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, hdegree v])
  exact (Fin.castAddEmb 1).trans (e.toEmbedding.trans (Function.Embedding.subtype _))

theorem incidentSelection_incident {V E : Type*} [Fintype E] [DecidableEq E]
    (left right : E → V) (d : ℕ)
    (hdegree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1)
    (v : V) (j : Fin d) : edgeIncident left right v (incidentSelection left right d hdegree v j) := by
  exact (Finset.mem_filter.mp
    ((Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, hdegree v]) :
      Fin (d+1) ≃ {e // e ∈ Finset.univ.filter (edgeIncident left right v)}) j.castSucc).property).2

def SourceCharge.withPrivate {I V E : Type*} [DecidableEq I] [DecidableEq V]
    [Fintype E] [DecidableEq E] {left right : E → V}
    {reads vertexView : V → Finset I} {edgeView : E → Finset I} {d : ℕ}
    (charge : SourceCharge left right reads vertexView edgeView d)
    (hdegree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1)
    (hcontains : ∀ v e, edgeIncident left right v e → vertexView v ⊆ edgeView e) :
    SourceCharge left right (privateReads reads) (fun v => rawView (vertexView v))
      (fun e => rawView (edgeView e)) d := by
  have hraw (i : I) (v : V) :
      Sum.inl i ∈ privateReads reads v ∧ Sum.inl i ∉ rawView (V := V) (vertexView v) ↔
        i ∈ reads v ∧ i ∉ vertexView v := by simp [privateReads, rawView]
  have hpriv (i v : V) :
      Sum.inr i ∈ privateReads reads v ∧ Sum.inr i ∉ rawView (V := V) (vertexView v) ↔ v = i := by
    simp [privateReads, rawView, eq_comm]
  let route : ∀ i : I ⊕ V,
      ({v // i ∈ privateReads reads v ∧ i ∉ rawView (V := V) (vertexView v)} × Fin d) ↪ E := by
    intro i
    cases i with
    | inl i =>
      exact ⟨fun z => charge.route i (⟨z.1.val,(hraw i z.1.val).mp z.1.property⟩,z.2), by
        intro a b h
        have he := (charge.route i).injective h
        exact Prod.ext (Subtype.ext (congrArg (fun z => z.1.val) he))
          (congrArg (fun z : {v // i ∈ reads v ∧ i ∉ vertexView v} × Fin d => z.2) he)⟩
    | inr i =>
      exact ⟨fun z => incidentSelection left right d hdegree i z.2, by
        intro a b h
        have hj := (incidentSelection left right d hdegree i).injective h
        exact Prod.ext (Subtype.ext (((hpriv i a.1.val).mp a.1.property).trans
          ((hpriv i b.1.val).mp b.1.property).symm)) hj⟩
  refine ⟨route,?_,?_,?_⟩
  · intro i z
    cases i with
    | inl i => exact charge.incident i _
    | inr i =>
      have h := incidentSelection_incident left right d hdegree i z.2
      have he := ((hpriv i z.1.val).mp z.1.property).symm
      exact h.elim (fun h => Or.inl (h.trans he)) (fun h => Or.inr (h.trans he))
  · intro i z
    cases i with
    | inl i =>
      exact Finset.map_subset_map.mpr
        (charge.contains i (⟨z.1.val,(hraw i z.1.val).mp z.1.property⟩,z.2))
    | inr i =>
      apply Finset.map_subset_map.mpr
      apply hcontains
      have h := incidentSelection_incident left right d hdegree i z.2
      have he := ((hpriv i z.1.val).mp z.1.property).symm
      exact h.elim (fun h => Or.inl (h.trans he)) (fun h => Or.inr (h.trans he))
  · intro i z
    cases i with
    | inl i =>
      simpa only [rawView, Finset.mem_map, Function.Embedding.inl_apply,
        Sum.inl.injEq, exists_eq_right] using (charge.fresh i
          (⟨z.1.val,(hraw i z.1.val).mp z.1.property⟩,z.2))
    | inr i => simp [rawView]

namespace FiniteProb

instance sumInputFintype {I J : Type*} {T : I → Type u} {R : J → Type u}
    [∀ i, Fintype (T i)] [∀ j, Fintype (R j)] : ∀ s : I ⊕ J, Fintype (Sum.elim T R s)
  | Sum.inl i => inferInstanceAs (Fintype (T i))
  | Sum.inr j => inferInstanceAs (Fintype (R j))

def sumProb {I J : Type*} {T : I → Type u} {R : J → Type u}
    [∀ i, Fintype (T i)] [∀ j, Fintype (R j)]
    (P : ∀ i, FiniteProb (T i)) (Q : ∀ j, FiniteProb (R j)) :
    ∀ s : I ⊕ J, FiniteProb (Sum.elim T R s)
  | Sum.inl i => P i
  | Sum.inr j => Q j

theorem pi_sum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {T : I → Type u} {R : J → Type u} [∀ i, Fintype (T i)] [∀ j, Fintype (R j)]
    (P : ∀ i, FiniteProb (T i)) (Q : ∀ j, FiniteProb (R j)) :
    (pi (sumProb P Q)).map (Equiv.sumPiEquivProdPi (Sum.elim T R)) = (pi P).product (pi Q) := by
  ext x
  rw [map_equiv_weight]
  simp only [pi, Fintype.prod_sum_type, Equiv.sumPiEquivProdPi_symm_apply, product, sumProb]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/StochasticEntropy.lean ===== -/

/-! Shannon's edge/vertex inequality for actual local stochastic kernels.
Independent private tables are constructed and routed, not assumed to obey
an entropy inequality. All types are finite; no rationality of weights is
required. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem table_edge_vertex_entropy {I V E A B : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype A] [Fintype B] [DecidableEq B]
    {T : I → Type} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (Y : V → (∀ i, T i) → B) (K : V → B → FiniteProb A)
    (left right : E → V) (reads vertexView : V → Finset I) (edgeView : E → Finset I) {d : ℕ}
    (hlocal : ∀ v, ReadsOnly (Y v) (reads v))
    (charge : SourceCharge left right reads vertexView edgeView d)
    (hdegree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1)
    (hcontains : ∀ v e, edgeIncident left right v e → vertexView v ⊆ edgeView e) :
    let ν := (pi P).product (tableProbability K)
    (d:ℝ)*(∑ v, ν.condEntropy (tableDraw Y v) (fun x => observeInputs (vertexView v) x.1)) ≤
      ∑ e, ν.condEntropy (fun x => (tableDraw Y (left e) x,tableDraw Y (right e) x))
        (fun x => observeInputs (edgeView e) x.1) := by
  let R : V → Type := fun _ => B → A
  let Q : ∀ v, FiniteProb (R v) := fun v => pi (K v)
  let split := Equiv.sumPiEquivProdPi (Sum.elim T R)
  let W := fun v x => tableDraw Y v (split x)
  have hW (v : V) : ReadsOnly (W v) (privateReads reads v) := by
    intro x z hxz
    have ht : x (Sum.inr v) = z (Sum.inr v) := hxz _ (by simp [privateReads])
    have hy : Y v (fun i => x (Sum.inl i)) = Y v (fun i => z (Sum.inl i)) := by
      apply hlocal v
      intro i hi
      exact hxz _ (by simp [privateReads, rawView, hi])
    change x (Sum.inr v) (Y v (fun i => x (Sum.inl i))) =
      z (Sum.inr v) (Y v (fun i => z (Sum.inl i)))
    rw [ht, hy]
  have h := conditional_edge_vertex_entropy_finite (sumProb P Q) W left right
    (privateReads reads) (fun v => rawView (vertexView v)) (fun e => rawView (edgeView e))
    hW (charge.withPrivate hdegree hcontains)
  have heq {C : Type} [Fintype C] (Z : ((∀ i, T i) × (V → B → A)) → C) (S : Finset I) :
      (pi (sumProb P Q)).condEntropy (fun x => Z (split x)) (observeInputs (rawView S)) =
        ((pi P).product (tableProbability K)).condEntropy Z (fun x => observeInputs S x.1) := by
    have hf : (pi (sumProb P Q)).condEntropy (fun x => Z (split x)) (observeInputs (rawView S)) =
        (pi (sumProb P Q)).condEntropy (fun x => Z (split x))
          (fun x => observeInputs S (split x).1) := by
      apply condEntropy_same_fibers
      intro x z
      rw [observeInputs_eq_iff, observeInputs_eq_iff]
      constructor
      · intro h i hi
        exact h (Sum.inl i) (by simp [rawView, hi])
      · intro h i hi
        rcases Finset.mem_map.mp hi with ⟨j,hj,rfl⟩
        exact h j hj
    rw [hf, ← condEntropy_map _ split Z (fun x => observeInputs S x.1)]
    change ((pi (sumProb P Q)).map (Equiv.sumPiEquivProdPi (Sum.elim T R))).condEntropy _ _ = _
    rw [pi_sum]
    rfl
  dsimp only
  have hp (e : E) := heq (fun x => (tableDraw Y (left e) x,tableDraw Y (right e) x)) (edgeView e)
  simpa only [W, hp, heq] using h

theorem symmetric_table_entropy {I V E A B : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype E] [DecidableEq E] [Fintype A] [Fintype B] [DecidableEq B]
    {T : I → Type} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (Y : V → (∀ i, T i) → B) (K : V → B → FiniteProb A)
    (left right : E → V) (reads vertexView : V → Finset I) (edgeView : E → Finset I) {d : ℕ}
    (hlocal : ∀ v, ReadsOnly (Y v) (reads v))
    (charge : SourceCharge left right reads vertexView edgeView d)
    (hdegree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1)
    (hcontains : ∀ v e, edgeIncident left right v e → vertexView v ⊆ edgeView e)
    (hcard : 2*Fintype.card E = (d+1)*Fintype.card V) {Hv He : ℝ}
    (hv : ∀ v, ((pi P).product (tableProbability K)).condEntropy (tableDraw Y v)
      (fun x => observeInputs (vertexView v) x.1) = Hv)
    (he : ∀ e, ((pi P).product (tableProbability K)).condEntropy
      (fun x => (tableDraw Y (left e) x,tableDraw Y (right e) x))
        (fun x => observeInputs (edgeView e) x.1) = He) :
    ((d:ℝ)+1)/2*He ≥ (d:ℝ)*Hv := by
  have h := table_edge_vertex_entropy P Y K left right reads vertexView edgeView hlocal charge hdegree hcontains
  dsimp only at h
  simp only [hv, he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hc : (Fintype.card E:ℝ) = ((d:ℝ)+1)*(Fintype.card V:ℝ)/2 := by
    have hc' : (2:ℝ)*Fintype.card E = ((d:ℝ)+1)*Fintype.card V := by exact_mod_cast hcard
    linarith
  rw [hc] at h
  have hp : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_left hp).mp
  convert h using 1 <;> ring

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/BernoulliRounding.lean ===== -/

/-! Independent private Bernoulli rounding of a local number in [0,1].
The two-point moment is the original expectation of the product, exactly. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteProb Bool where
  weight b := if b then p else 1-p
  nonneg b := by cases b <;> simp_all
  total := by simp [Fintype.sum_bool]

@[simp] theorem bernoulli_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulli p hp0 hp1).prob (fun b => b = true) = p := by
  simp [prob, expect, bernoulli, Fintype.sum_bool, bit]

variable {Ω I B : Type*} [Fintype Ω] [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]

theorem bernoulli_table_mean (μ : FiniteProb Ω) (Y : I → Ω → B) (f : I → B → ℝ)
    (hf0 : ∀ i b, 0 ≤ f i b) (hf1 : ∀ i b, f i b ≤ 1) (i : I) :
    (μ.product (tableProbability (fun i b => bernoulli (f i b) (hf0 i b) (hf1 i b)))).prob
      (fun x => tableDraw Y i x = true) = μ.expect (fun ω => f i (Y i ω)) := by
  rw [prob, product_expect]
  apply μ.expect_congr
  intro ω
  exact (table_expect_one _ i (Y i ω) (fun b => bit (b=true))).trans (bernoulli_true _ _ _)

theorem bernoulli_table_moment (μ : FiniteProb Ω) (Y : I → Ω → B) (f : I → B → ℝ)
    (hf0 : ∀ i b, 0 ≤ f i b) (hf1 : ∀ i b, f i b ≤ 1) (i j : I) (hji : j ≠ i) :
    (μ.product (tableProbability (fun i b => bernoulli (f i b) (hf0 i b) (hf1 i b)))).prob
      (fun x => tableDraw Y i x = true ∧ tableDraw Y j x = true) =
        μ.expect (fun ω => f i (Y i ω)*f j (Y j ω)) := by
  rw [prob, product_expect]
  apply μ.expect_congr
  intro ω
  have he (t : I → B → Bool) :
      bit (tableDraw Y i (ω,t) = true ∧ tableDraw Y j (ω,t) = true) =
        bit (t i (Y i ω) = true)*bit (t j (Y j ω) = true) := by
    by_cases hi : t i (Y i ω) = true <;> by_cases hj : t j (Y j ω) = true <;>
      simp [tableDraw, bit, hi, hj]
  rw [expect_congr _ he, table_expect_pair _ i j hji (Y i ω) (Y j ω)
    (fun b => bit (b=true)) (fun b => bit (b=true))]
  change (bernoulli _ _ _).prob _ * (bernoulli _ _ _).prob _ = _
  rw [bernoulli_true, bernoulli_true]

/-- The scalar estimate follows from the Shannon inequality for the
constructed private-table experiment. The Shannon premise is discharged by
source charging when the views and the field have the required geometry. -/
theorem scalar_moment_from_rounding (μ : FiniteProb Ω) (Y : I → Ω → B) (f : I → B → ℝ)
    (hf0 : ∀ i b, 0 ≤ f i b) (hf1 : ∀ i b, f i b ≤ 1) (i j : I) (hji : j ≠ i)
    {D p : ℝ} (hD : 0 < D)
    (hi : μ.expect (fun ω => f i (Y i ω)) = p) (hj : μ.expect (fun ω => f j (Y j ω)) = p)
    (htree : let ν := μ.product (tableProbability (fun i b => bernoulli (f i b) (hf0 i b) (hf1 i b)))
      (D/2)*ν.entropyOf (fun x => (tableDraw Y i x,tableDraw Y j x)) ≥
        (D-1)*ν.entropyOf (tableDraw Y i)) :
    p^2/2-2*binaryEntropy p/D ≤ μ.expect (fun ω => f i (Y i ω)*f j (Y j ω)) := by
  have h := scalar_pair_overlap
    (μ.product (tableProbability (fun i b => bernoulli (f i b) (hf0 i b) (hf1 i b))))
    (tableDraw Y i) (tableDraw Y j) hD
    ((bernoulli_table_mean μ Y f hf0 hf1 i).trans hi)
    ((bernoulli_table_mean μ Y f hf0 hf1 j).trans hj) htree
  rwa [bernoulli_table_moment μ Y f hf0 hf1 i j hji] at h

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/AncestorSequence.lean ===== -/

/-! Constructed first-deletion parts of the original output. These are not
the realized resampled draws. Their conditional distributions will be used
to define the successive smaller-radius stochastic rules. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem restrictOutput_some_original {A : Type*} (P : A → Prop) (x : Option A)
    {a : A} (h : restrictOutput P x = some a) : x = some a :=
  (restrictOutput_eq_some P x a).mp h |>.1

theorem selectedConflict_of_restriction {C A B : Type*} (E : C → A → B → Prop)
    (c : C) (u u' : Option A) (v v' : Option B)
    (hu : ∀ a, u' = some a → u = some a) (hv : ∀ b, v' = some b → v = some b) :
    selectedConflict E (c,u',v') → selectedConflict E (c,u,v) := by
  cases u' with
  | none => simp [selectedConflict]
  | some a =>
    cases v' with
    | none => simp [selectedConflict]
    | some b => simp [selectedConflict, hu a rfl, hv b rfl]

namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

def survivor (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m : ℕ) :
    ℕ → Ω → Option A
  | 0 => U
  | n+1 => μ.keptOutput (μ.survivor U Y m n) (Y n) m

def firstDeleted (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m n : ℕ) :
    Ω → Option A := μ.deletedOutput (μ.survivor U Y m n) (Y n) m

theorem survivor_some_original (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (ω : Ω) (a : A) :
    μ.survivor U Y m n ω = some a → U ω = some a := by
  induction n with
  | zero => exact id
  | succ n ih =>
    intro h
    exact ih (restrictOutput_some_original _ _ h)

theorem firstDeleted_some_survivor (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (ω : Ω) (a : A) :
    μ.firstDeleted U Y m n ω = some a → μ.survivor U Y m n ω = some a :=
  restrictOutput_some_original _ _

theorem firstDeleted_some_original (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (ω : Ω) (a : A) :
    μ.firstDeleted U Y m n ω = some a → U ω = some a := fun h =>
  μ.survivor_some_original U Y m n ω a (μ.firstDeleted_some_survivor U Y m n ω a h)

theorem ancestor_mass_partition (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) :
    μ.prob (fun ω => μ.survivor U Y m n ω ≠ none) +
      ∑ j ∈ Finset.range n, μ.prob (fun ω => μ.firstDeleted U Y m j ω ≠ none) =
        μ.prob (fun ω => U ω ≠ none) := by
  induction n with
  | zero => simp [survivor]
  | succ n ih =>
    have h := μ.kept_deleted_mass (μ.survivor U Y m n) (Y n) m
    change μ.prob (fun ω => μ.survivor U Y m (n+1) ω ≠ none) +
      μ.prob (fun ω => μ.firstDeleted U Y m n ω ≠ none) = _ at h
    rw [Finset.sum_range_succ]
    linarith

def budgetPart (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m n : ℕ) :
    Option (Fin n) → Ω → Option A
  | none => μ.survivor U Y m (n+1)
  | some i => μ.firstDeleted U Y m (i.val+1)

def budgetView (Y : ℕ → Ω → B) (n : ℕ) : Option (Fin n) → Ω → B
  | none => Y n
  | some i => Y i.val

theorem budgetPart_mass (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m n : ℕ) :
    (∑ i, μ.prob (fun ω => μ.budgetPart U Y m n i ω ≠ none)) +
      μ.prob (fun ω => μ.firstDeleted U Y m 0 ω ≠ none) = μ.prob (fun ω => U ω ≠ none) := by
  have h := μ.ancestor_mass_partition U Y m (n+1)
  rw [Finset.sum_range_succ'] at h
  simp only [budgetPart, Fintype.sum_option,
    Fin.sum_univ_eq_sum_range (fun i => μ.prob (fun ω => μ.firstDeleted U Y m (i+1) ω ≠ none)) n]
  linarith

theorem budgetPart_mass_le (μ : FiniteProb Ω) (U : Ω → Option A) (Y : ℕ → Ω → B) (m n : ℕ) :
    (∑ i, μ.prob (fun ω => μ.budgetPart U Y m n i ω ≠ none)) ≤ μ.prob (fun ω => U ω ≠ none) := by
  have h := μ.budgetPart_mass U Y m n
  linarith [μ.prob_nonneg (fun ω => μ.firstDeleted U Y m 0 ω ≠ none)]

theorem budgetPart_some_original (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (i : Option (Fin n)) (ω : Ω) (a : A) :
    μ.budgetPart U Y m n i ω = some a → U ω = some a := by
  cases i with
  | none => exact μ.survivor_some_original U Y m (n+1) ω a
  | some i => exact μ.firstDeleted_some_original U Y m (i.val+1) ω a

theorem survivor_short_support (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (b : B) (hb : 0 < (μ.map (Y n)).weight b) (a : A)
    (ha : a ∉ ((μ.given (Y n) b).map (μ.survivor U Y m n)).outputList m) :
    ((μ.given (Y n) b).map (μ.survivor U Y m (n+1))).weight (some a) = 0 :=
  μ.kept_given_support (μ.survivor U Y m n) (Y n) m b hb a ha

theorem firstDeleted_short_support (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : ℕ → Ω → B) (m n : ℕ) (b : B) (hb : 0 < (μ.map (Y n)).weight b) (a : A)
    (ha : a ∉ ((μ.given (Y n) b).map (μ.survivor U Y m n)).outputList m) :
    ((μ.given (Y n) b).map (μ.firstDeleted U Y m (n+1))).weight (some a) = 0 := by
  apply le_antisymm _ (((μ.given (Y n) b).map _).nonneg _)
  calc
    _ ≤ ((μ.given (Y n) b).map (μ.survivor U Y m (n+1))).weight (some a) :=
      (μ.given (Y n) b).prob_mono (fun ω h =>
        μ.firstDeleted_some_survivor U Y m (n+1) ω a h)
    _ = 0 := μ.survivor_short_support U Y m n b hb a ha

omit [Fintype C] in
theorem budgetPart_zero_conflict (μ : FiniteProb Ω) (U V : Ω → Option A)
    (Y Z : ℕ → Ω → B) (m n : ℕ) (F : Ω → C) (E : C → A → A → Prop)
    (hz : μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) = 0) (i : Option (Fin n)) :
    μ.prob (fun ω => selectedConflict E
      (F ω,μ.budgetPart U Y m n i ω,μ.budgetPart V Z m n i ω)) = 0 := by
  apply le_antisymm _ (μ.prob_nonneg _)
  calc
    _ ≤ μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) := μ.prob_mono (fun ω =>
      selectedConflict_of_restriction E _ _ _ _ _
        (μ.budgetPart_some_original U Y m n i ω) (μ.budgetPart_some_original V Z m n i ω))
    _ = 0 := hz

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/TruncationEstimate.lean ===== -/

/-! Assembly of the robust one-layer estimate. Failure costs are weighted by
the local occupancy surrogate, so their total is proportional to its mean. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

theorem tails_cover_product {a b x y : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a*b ≤ x*y+a*bit (x<a)+b*bit (y<b) := by
  have hxy := mul_nonneg hx hy
  by_cases ha : x < a
  · have hab := mul_le_mul_of_nonneg_left hb1 ha0
    have hf := mul_nonneg hb0 (bit_nonneg (y<b))
    simp only [bit, ha, if_true, mul_one] at *
    linarith
  · by_cases hb : y < b
    · have hab := mul_le_mul_of_nonneg_right ha1 hb0
      simp only [bit, ha, hb, if_false, if_true, mul_zero, mul_one]
      linarith
    · simp only [bit, ha, hb, if_false, mul_zero, add_zero]
      exact mul_le_mul (le_of_not_gt ha) (le_of_not_gt hb) hb0 hx

namespace FiniteProb

variable {Ω A B C I : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype I]

theorem weighted_branch_at (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : Ω → B) (F : I → Ω → C) (coarse : I → C → B)
    (href : ∀ i ω, Y ω = coarse i (F i ω)) (ell M m : ℕ)
    (hD : 12 ≤ (Fintype.card I : ℝ)) (hlog : 1 ≤ Real.log (Fintype.card I : ℝ))
    (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*Fintype.card I ≤ (Fintype.card I : ℝ)^4)
    (hratio : (M:ℝ)/m = 1/(Fintype.card I : ℝ))
    (hind : ∀ b, 0 < (μ.map Y).weight b → (μ.given Y b).Independent F)
    (hatom : ∀ b, 0 < (μ.map Y).weight b → ∀ a,
      ((μ.given Y b).map U).weight (some a) ≤ 1/(m:ℝ)) (i₀ : I)
    (hsym : ∀ i, μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω) *
      bit (((μ.given (F i) (F i ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) (Y ω))) =
      μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω) *
      bit (((μ.given (F i₀) (F i₀ ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) (Y ω)))) :
    μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω) *
      bit (((μ.given (F i₀) (F i₀ ω)).map U).tail ell <
        μ.occupancyScalar U Y (Fintype.card I) (Y ω))) ≤
      (256*Real.log (Fintype.card I : ℝ)/(Fintype.card I : ℝ)) *
        μ.expect (fun ω => μ.occupancyScalar U Y (Fintype.card I) (Y ω)) := by
  have h := μ.weighted_branch_failures U Y F coarse href ell M m hD hlog hM hm hellM hsize hratio hind hatom
  simp only [hsym, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hd : (0:ℝ) < Fintype.card I := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem expected_product_from_tails (μ : FiniteProb Ω) (f g x y : Ω → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hf1 : ∀ ω, f ω ≤ 1)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1)
    (hx : ∀ ω, 0 ≤ x ω) (hy : ∀ ω, 0 ≤ y ω)
    {a b c : ℝ} (htail : μ.expect (fun ω => x ω*y ω) ≤ a)
    (hfail : μ.expect (fun ω => f ω*bit (x ω<f ω)) ≤ b)
    (hfail' : μ.expect (fun ω => g ω*bit (y ω<g ω)) ≤ c) :
    μ.expect (fun ω => f ω*g ω) ≤ a+b+c := by
  have h := μ.expect_mono (fun ω => tails_cover_product (hf0 ω) (hf1 ω) (hg0 ω) (hg1 ω) (hx ω) (hy ω))
  rw [expect_add, expect_add] at h
  linarith

omit [Fintype A] in
/-- Final assembly of one robust truncation step. The tail, branch and scalar
estimates in the premises are the conclusions of separately checked lemmas;
this statement makes their exact interface and constants visible. -/
theorem truncation_from_local_moments (μ : FiniteProb Ω) (U : Ω → Option A)
    (Y : Ω → B) (g x y : Ω → ℝ) {D w q : ℝ}
    (hD : 0 < D) (hlog : 1 ≤ Real.log D) (hw : 0 ≤ w) (hq : q ≤ 1/D^2)
    (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1)
    (hx : ∀ ω, 0 ≤ x ω) (hy : ∀ ω, 0 ≤ y ω)
    (htail : μ.expect (fun ω => x ω*y ω) ≤ 4*w+q)
    (hfail : μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω) *
      bit (x ω < μ.occupancyScalar U Y D (Y ω))) ≤
        (256*Real.log D/D)*μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)))
    (hfail' : μ.expect (fun ω => g ω*bit (y ω<g ω)) ≤
        (256*Real.log D/D)*μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)))
    (hscalar : (μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)))^2/2 -
      2*binaryEntropy (μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)))/D ≤
        μ.expect (fun ω => μ.occupancyScalar U Y D (Y ω)*g ω)) :
    μ.prob (fun ω => U ω ≠ none) ≤ 2100*Real.log D/D+6*Real.sqrt w := by
  have hup := μ.expected_product_from_tails (fun ω => μ.occupancyScalar U Y D (Y ω)) g x y
    (fun ω => μ.occupancyScalar_nonneg U Y D (Y ω))
    (fun ω => μ.occupancyScalar_le_one U Y hD (Y ω)) hg0 hg1 hx hy htail hfail hfail'
  apply truncation_moment_bound hD hlog
    (μ.expect_le_const (fun ω => μ.occupancyScalar_le_one U Y hD (Y ω))) hw hq
    (μ.occupancyScalar_mass U Y D)
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/SymmetryTransport.lean ===== -/

/-! Symmetry of actual conditional distributions and the constructed ancestor
sequence. Null fibers are included: both sides use the same fallback marginal.
This is a distribution identity, not an assumed entropy inequality. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

theorem expect_invariant (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ) (f : Ω → ℝ) :
    μ.expect (fun ω => f (e ω)) = μ.expect f := by
  rw [← μ.expect_map e f, he]

theorem prob_invariant (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ) (E : Ω → Prop) :
    μ.prob (fun ω => E (e ω)) = μ.prob E := μ.expect_invariant e he (fun ω => bit (E ω))

theorem map_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (X X' : Ω → A) (hX : ∀ ω, X' (e ω) = X ω) : μ.map X' = μ.map X := by
  nth_rw 1 [← he]
  rw [map_comp]
  exact congrArg (map μ) (funext hX)

theorem given_map_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (X X' : Ω → A) (Y Y' : Ω → B) (β : B ≃ B)
    (hX : ∀ ω, X' (e ω) = X ω) (hY : ∀ ω, Y' (e ω) = β (Y ω)) (b : B) :
    (μ.given Y' (β b)).map X' = (μ.given Y b).map X := by
  have hmass : (μ.map Y').weight (β b) = (μ.map Y).weight b := by
    change μ.prob (fun ω => Y' ω = β b) = μ.prob (fun ω => Y ω = b)
    rw [← μ.prob_invariant e he (fun ω => Y' ω = β b)]
    exact μ.prob_congr (fun ω => by rw [hY, β.injective.eq_iff])
  by_cases hb : 0 < (μ.map Y).weight b
  · have hb' : 0 < (μ.map Y').weight (β b) := by rwa [hmass]
    ext a
    rw [given_pair_mass _ X' Y' a (β b) hb', given_pair_mass _ X Y a b hb, hmass]
    congr 1
    change μ.prob (fun ω => (X' ω,Y' ω) = (a,β b)) = μ.prob (fun ω => (X ω,Y ω) = (a,b))
    rw [← μ.prob_invariant e he (fun ω => (X' ω,Y' ω) = (a,β b))]
    apply μ.prob_congr
    intro ω
    simp only [hX, hY, Prod.mk.injEq, β.injective.eq_iff]
  · have hb' : ¬ 0 < (μ.map Y').weight (β b) := by rwa [hmass]
    simp only [given, hb, hb', dif_neg]
    exact μ.map_transport e he X X' hX

theorem keptOutput_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : Ω → B) (β : B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ ω, Y' (e ω) = β (Y ω)) (m : ℕ) (ω : Ω) :
    μ.keptOutput U' Y' m (e ω) = μ.keptOutput U Y m ω := by
  unfold keptOutput
  rw [hU, hY, μ.given_map_transport e he U U' Y Y' β hU hY]

theorem deletedOutput_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : Ω → B) (β : B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ ω, Y' (e ω) = β (Y ω)) (m : ℕ) (ω : Ω) :
    μ.deletedOutput U' Y' m (e ω) = μ.deletedOutput U Y m ω := by
  unfold deletedOutput
  rw [hU, hY, μ.given_map_transport e he U U' Y Y' β hU hY]

theorem survivor_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : ℕ → Ω → B) (β : ℕ → B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ n ω, Y' n (e ω) = β n (Y n ω)) (m n : ℕ) :
    ∀ ω, μ.survivor U' Y' m n (e ω) = μ.survivor U Y m n ω := by
  induction n with
  | zero => exact hU
  | succ n ih => exact μ.keptOutput_transport e he _ _ _ _ (β n) ih (hY n) m

theorem firstDeleted_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : ℕ → Ω → B) (β : ℕ → B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ n ω, Y' n (e ω) = β n (Y n ω)) (m n : ℕ) :
    ∀ ω, μ.firstDeleted U' Y' m n (e ω) = μ.firstDeleted U Y m n ω :=
  μ.deletedOutput_transport e he _ _ _ _ (β n) (μ.survivor_transport e he U U' Y Y' β hU hY m n)
    (hY n) m

theorem entropy_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (X X' : Ω → A) (α : A ≃ A) (hX : ∀ ω, X' (e ω) = α (X ω)) :
    μ.entropyOf X' = μ.entropyOf X := by
  nth_rw 1 [← he]
  rw [entropyOf_map]
  rw [μ.entropyOf_congr hX]
  exact μ.entropyOf_comp_injective X α α.injective

theorem conditional_entropy_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (X X' : Ω → A) (Y Y' : Ω → B) (α : A ≃ A) (β : B ≃ B)
    (hX : ∀ ω, X' (e ω) = α (X ω)) (hY : ∀ ω, Y' (e ω) = β (Y ω)) :
    μ.condEntropy X' Y' = μ.condEntropy X Y := by
  unfold condEntropy
  rw [μ.entropy_transport e he (fun ω => (X ω,Y ω)) (fun ω => (X' ω,Y' ω))
      (α.prodCongr β) (fun ω => Prod.ext (hX ω) (hY ω)),
    μ.entropy_transport e he Y Y' β hY]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/FiniteKernels.lean ===== -/

/-! Finite probability kernels, their private-table realization, and exact
averaging identities. Kernel weights may be arbitrary real probabilities. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C V : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype V]

def bind (μ : FiniteProb Ω) (K : Ω → FiniteProb A) : FiniteProb A where
  weight a := μ.expect (fun ω => (K ω).weight a)
  nonneg a := μ.expect_nonneg (fun ω => (K ω).nonneg a)
  total := by
    rw [← expect_sum]
    simp only [FiniteProb.total, expect_const]

theorem expect_bind (μ : FiniteProb Ω) (K : Ω → FiniteProb A) (f : A → ℝ) :
    (μ.bind K).expect f = μ.expect (fun ω => (K ω).expect f) := by
  simp only [bind, expect, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext ω
  congr 1
  funext a
  ring

theorem bind_map (μ : FiniteProb Ω) (K : Ω → FiniteProb A) (f : A → B) :
    (μ.bind K).map f = μ.bind (fun ω => (K ω).map f) := by
  ext b
  exact μ.expect_bind K (fun a => bit (f a=b))

theorem product_map_bind (μ : FiniteProb Ω) (Q : FiniteProb A) (X : Ω × A → B) :
    (μ.product Q).map X = μ.bind (fun ω => Q.map (fun a => X (ω,a))) := by
  ext b
  exact product_expect μ Q (fun x => bit (X x=b))

theorem bind_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (K K' : Ω → FiniteProb A) (α : A ≃ A)
    (hK : ∀ ω, K' (e ω) = (K ω).map α) : μ.bind K' = (μ.bind K).map α := by
  rw [bind_map]
  ext a
  change μ.expect (fun ω => (K' ω).weight a) = μ.expect (fun ω => ((K ω).map α).weight a)
  rw [← μ.expect_invariant e he (fun ω => (K' ω).weight a)]
  exact μ.expect_congr (fun ω => congrArg (fun P => P.weight a) (hK ω))

def mixedPair (μ : FiniteProb Ω) (F : Ω → C) (K L : Ω → FiniteProb A) :
    FiniteProb (C × A × A) :=
  μ.bind (fun ω => ((K ω).product (L ω)).map (fun ab => (F ω,ab.1,ab.2)))

theorem table_mixedPair [DecidableEq V] [DecidableEq B]
    (μ : FiniteProb Ω) (Y : V → Ω → B) (K : V → B → FiniteProb A)
    (i j : V) (hji : j ≠ i) (F : Ω → C) :
    (μ.product (tableProbability K)).map (fun x => (F x.1,tableDraw Y i x,tableDraw Y j x)) =
      μ.mixedPair F (fun ω => K i (Y i ω)) (fun ω => K j (Y j ω)) := by
  rw [product_map_bind]
  congr 1
  funext ω
  change (tableProbability K).map (fun t => (F ω,t i (Y i ω),t j (Y j ω))) = _
  rw [← map_comp (tableProbability K) (fun t => (t i (Y i ω),t j (Y j ω)))
      (fun ab : A × A => (F ω,ab.1,ab.2)),
    table_pair_distribution K i j hji]

theorem mixedPair_weight (μ : FiniteProb Ω) (F : Ω → C) (K L : Ω → FiniteProb A)
    (c : C) (a b : A) :
    (μ.mixedPair F K L).weight (c,a,b) =
      μ.expect (fun ω => bit (F ω=c)*(K ω).weight a*(L ω).weight b) := by
  apply μ.expect_congr
  intro ω
  change ((K ω).product (L ω)).prob (fun ab => (F ω,ab.1,ab.2) = (c,a,b)) = _
  by_cases hf : F ω=c
  · simp [prob, expect, product, Fintype.sum_prod_type, bit, hf]
  · simp [prob, expect, product, Fintype.sum_prod_type, bit, hf]

/-- If the shared observation contains the endpoint views, the independently
sampled pair has exactly the direct-projection distribution used in the KL
budget. No equality of realized original and sampled outputs is claimed. -/
theorem sampled_is_projectedPair [DecidableEq V] [DecidableEq B]
    (μ : FiniteProb Ω) (U : V → Ω → A) (Y : V → Ω → B)
    (i j : V) (hji : j ≠ i) (F : Ω → C) (yi yj : C → B)
    (hi : ∀ ω, Y i ω = yi (F ω)) (hj : ∀ ω, Y j ω = yj (F ω)) :
    let K := fun v b => (μ.given (Y v) b).map (U v)
    (μ.product (tableProbability K)).map (fun x => (F x.1,tableDraw Y i x,tableDraw Y j x)) =
      μ.projectedPair F (U i) (U j) yi yj := by
  dsimp only
  rw [table_mixedPair μ Y _ i j hji F]
  have hYi : Y i = fun ω => yi (F ω) := funext hi
  have hYj : Y j = fun ω => yj (F ω) := funext hj
  ext t
  rcases t with ⟨c,a,b⟩
  rw [mixedPair_weight]
  have hpoint (ω : Ω) : bit (F ω=c)*((μ.given (Y i) (Y i ω)).map (U i)).weight a *
      ((μ.given (Y j) (Y j ω)).map (U j)).weight b =
      (((μ.given (Y i) (yi c)).map (U i)).weight a *
        ((μ.given (Y j) (yj c)).map (U j)).weight b)*bit (F ω=c) := by
    by_cases hf : F ω=c
    · rw [hi ω, hj ω, hf]
      ring
    · simp [bit, hf]
  rw [μ.expect_congr hpoint, expect_mul]
  simp only [hYi, hYj, projectedPair, prob, map]
  ring

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/ProjectedTails.lean ===== -/

/-! Dense-tail control after projection. The original endpoint outputs may
remain correlated beyond the shared view. Only the two current input views
must be conditionally independent. This is what permits arbitrarily many
ancestor restrictions without pretending that they remain low-radius draws. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

omit [Fintype B] in
theorem Independent.bool_product {Y : Bool → Ω → B} {μ : FiniteProb Ω}
    (h : μ.Independent Y) (f g : B → ℝ) :
    μ.expect (fun ω => f (Y false ω)*g (Y true ω)) =
      μ.expect (fun ω => f (Y false ω))*μ.expect (fun ω => g (Y true ω)) := by
  have he := h (fun b => if b then g else f)
  simpa only [Fintype.prod_bool, Bool.false_eq_true, if_true, if_false, mul_comm] using he

theorem given_tower_refinement (μ : FiniteProb Ω) (Y : Ω → B) (F : Ω → C)
    (coarse : B → C) (hF : ∀ ω, F ω = coarse (Y ω)) (b : C)
    (hb : 0 < (μ.map F).weight b) (f : Ω → ℝ) :
    (μ.given F b).expect (fun ω => (μ.given Y (Y ω)).expect f) = (μ.given F b).expect f := by
  have he : F = fun ω => coarse (Y ω) := funext hF
  subst F
  exact μ.given_tower Y coarse b hb f

def kernelConflict (μ : FiniteProb Ω) (K L : Ω → FiniteProb (Option A))
    (G : Ω → A × A → Bool) : ℝ :=
  μ.expect (fun ω => ∑ a, ∑ b, (K ω).weight (some a)*(L ω).weight (some b)*bit (G ω (a,b)=true))

theorem kernelConflict_nonneg (μ : FiniteProb Ω) (K L : Ω → FiniteProb (Option A))
    (G : Ω → A × A → Bool) : 0 ≤ μ.kernelConflict K L G := by
  apply μ.expect_nonneg
  intro ω
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (mul_nonneg ((K ω).nonneg _) ((L ω).nonneg _)) (bit_nonneg _)))

/-- Average product of the two shared-fiber endpoint probabilities equals
the conflict probability of the CURRENT projected kernels. Independence of
the original outputs is neither assumed nor needed. -/
theorem projected_shared_conflict (μ : FiniteProb Ω) (U V : Ω → Option A)
    (Y Z : Ω → B) (F : Ω → C) (fy fz : B → C)
    (hfy : ∀ ω, F ω = fy (Y ω)) (hfz : ∀ ω, F ω = fz (Z ω))
    (hind : ∀ b, 0 < (μ.map F).weight b →
      (μ.given F b).Independent (fun t : Bool => if t then Z else Y)) (G : C → A × A → Bool) :
    (μ.map F).expect (fun b =>
      (((μ.given F b).map U).product ((μ.given F b).map V)).prob
        (fun ab => selectedConflict (fun _ : Unit => fun a a' => G b (a,a')=true) ((),ab.1,ab.2))) =
      μ.kernelConflict (fun ω => (μ.given Y (Y ω)).map U)
        (fun ω => (μ.given Z (Z ω)).map V) (fun ω => G (F ω)) := by
  let H := fun ω => ∑ a, ∑ b, ((μ.given Y (Y ω)).map U).weight (some a) *
    ((μ.given Z (Z ω)).map V).weight (some b)*bit (G (F ω) (a,b)=true)
  have hpoint (c : C) (hc : 0 < (μ.map F).weight c) :
      (((μ.given F c).map U).product ((μ.given F c).map V)).prob
        (fun ab => selectedConflict (fun _ : Unit => fun a a' => G c (a,a')=true) ((),ab.1,ab.2)) =
      (μ.given F c).expect H := by
    rw [product_selected_probability]
    have he : (μ.given F c).expect H = (μ.given F c).expect (fun ω => ∑ a, ∑ b,
        ((μ.given Y (Y ω)).map U).weight (some a)*((μ.given Z (Z ω)).map V).weight (some b)*
          bit (G c (a,b)=true)) := by
      apply (μ.given F c).expect_congr_on_support
      intro ω hω
      dsimp [H]
      rw [μ.given_support_eq F c hc hω]
    rw [he, expect_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [expect_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hind' := (hind c hc).bool_product
      (fun y => ((μ.given Y y).map U).weight (some a))
      (fun z => ((μ.given Z z).map V).weight (some b))
    simp only [Bool.false_eq_true, if_false, if_true] at hind'
    have hu := μ.given_tower_refinement Y F fy hfy c hc (fun ω => bit (U ω=some a))
    have hv := μ.given_tower_refinement Z F fz hfz c hc (fun ω => bit (V ω=some b))
    change (μ.given F c).expect (fun ω => ((μ.given Y (Y ω)).map U).weight (some a)) =
      ((μ.given F c).map U).weight (some a) at hu
    change (μ.given F c).expect (fun ω => ((μ.given Z (Z ω)).map V).weight (some b)) =
      ((μ.given F c).map V).weight (some b) at hv
    rw [hu, hv] at hind'
    calc
      _ = bit (G c (a,b)=true) * (μ.given F c).expect (fun ω =>
          ((μ.given Y (Y ω)).map U).weight (some a)*((μ.given Z (Z ω)).map V).weight (some b)) := by
        rw [hind']; ring
      _ = _ := by
        rw [← expect_mul]
        apply (μ.given F c).expect_congr
        intro ω
        ring
  rw [(μ.map F).expect_congr_on_support _ _ hpoint]
  exact μ.total_conditional_expectation F H

theorem projected_endpoint_tails [DecidableEq A] (μ : FiniteProb Ω)
    (U V : Ω → Option A) (Y Z : Ω → B) (F : Ω → C) (fy fz : B → C)
    (hfy : ∀ ω, F ω = fy (Y ω)) (hfz : ∀ ω, F ω = fz (Z ω))
    (hind : ∀ b, 0 < (μ.map F).weight b →
      (μ.given F b).Independent (fun t : Bool => if t then Z else Y))
    (G : C → A × A → Bool) {ell : ℕ} (hell : 0 < ell) {q : ℝ}
    (hbad : μ.prob (fun ω => exceptionalMatrix ell (G (F ω))) ≤ q) :
    μ.expect (fun ω => ((μ.given F (F ω)).map U).tail ell*((μ.given F (F ω)).map V).tail ell) ≤
      4*μ.kernelConflict (fun ω => (μ.given Y (Y ω)).map U)
        (fun ω => (μ.given Z (Z ω)).map V) (fun ω => G (F ω))+q := by
  have h := (μ.map F).expect_mono (fun b =>
    matrix_tail_product ((μ.given F b).map U) ((μ.given F b).map V) (G b) hell)
  rw [expect_add, expect_mul, μ.projected_shared_conflict U V Y Z F fy fz hfy hfz hind G,
    expect_map] at h
  change _ ≤ 4*μ.kernelConflict _ _ _ + (μ.map F).prob (fun b => exceptionalMatrix ell (G b)) at h
  rw [prob_map] at h
  linarith

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/LocalScalarMoment.lean ===== -/

/-! A scalar overlap bound derived from independent sources and geometric
routing. There is no entropy-inequality premise in the final theorem. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem bool_pair_ext (P Q : FiniteProb (Bool × Bool))
    (hfst : P.prob (fun ab => ab.1=true) = Q.prob (fun ab => ab.1=true))
    (hsnd : P.prob (fun ab => ab.2=true) = Q.prob (fun ab => ab.2=true))
    (hpair : P.prob (fun ab => ab.1=true ∧ ab.2=true) =
      Q.prob (fun ab => ab.1=true ∧ ab.2=true)) : P = Q := by
  have hP := P.total
  have hQ := Q.total
  simp only [prob, expect, Fintype.sum_prod_type, Fintype.sum_bool] at hfst hsnd hpair hP hQ
  norm_num [bit] at hfst hsnd hpair
  ext ab
  rcases ab with ⟨a,b⟩
  cases a <;> cases b <;> linarith

theorem entropyOf_const {Ω A : Type*} [Fintype Ω] [Fintype A] (μ : FiniteProb Ω) (a : A) :
    μ.entropyOf (fun _ => a) = 0 := by
  rw [entropyOf_eq_expect]
  have hm : (μ.map (fun _ => a)).weight a = 1 := by simp [map]
  simp [hm]

theorem condEntropy_const {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (μ : FiniteProb Ω) (X : Ω → A) (b : B) : μ.condEntropy X (fun _ => b) = μ.entropyOf X := by
  rw [condEntropy, entropyOf_const, sub_zero, entropy_pair_comm]
  exact μ.entropy_deterministic_pair X (fun _ => b)

theorem scalar_overlap_from_sources {I V E B : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
    {T : I → Type} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (Y : V → (∀ i, T i) → B) (f : V → B → ℝ)
    (hf0 : ∀ v b, 0 ≤ f v b) (hf1 : ∀ v b, f v b ≤ 1)
    (left right : E → V) (reads : V → Finset I) {d : ℕ}
    (hlocal : ∀ v, ReadsOnly (Y v) (reads v))
    (charge : SourceCharge left right reads (fun _ => ∅) (fun _ => ∅) d)
    (hdegree : ∀ v, (Finset.univ.filter (edgeIncident left right v)).card = d+1)
    (hcard : 2*Fintype.card E = (d+1)*Fintype.card V)
    (hne : ∀ e, right e ≠ left e) (e₀ : E) {p c : ℝ}
    (hmean : ∀ v, (pi P).expect (fun ω => f v (Y v ω)) = p)
    (hmoment : ∀ e, (pi P).expect (fun ω => f (left e) (Y (left e) ω)*f (right e) (Y (right e) ω)) = c) :
    p^2/2-2*binaryEntropy p/((d:ℝ)+1) ≤ c := by
  let K := fun v b => bernoulli (f v b) (hf0 v b) (hf1 v b)
  let ν := (pi P).product (tableProbability K)
  let Z := tableDraw (A := Bool) Y
  have hmeans (v : V) : ν.prob (fun x => Z v x=true) = p :=
    (bernoulli_table_mean (pi P) Y f hf0 hf1 v).trans (hmean v)
  have hmoments (e : E) : ν.prob (fun x => Z (left e) x=true ∧ Z (right e) x=true) = c :=
    (bernoulli_table_moment (pi P) Y f hf0 hf1 _ _ (hne e)).trans (hmoment e)
  have hv (v : V) : ν.entropyOf (Z v) = binaryEntropy p := by
    change (ν.map (Z v)).entropy = _
    rw [bool_entropy]
    exact congrArg binaryEntropy (hmeans v)
  have he (e : E) : ν.entropyOf (fun x => (Z (left e) x,Z (right e) x)) =
      ν.entropyOf (fun x => (Z (left e₀) x,Z (right e₀) x)) := by
    apply congrArg entropy
    apply bool_pair_ext
    · simp only [prob_map, hmeans]
    · simp only [prob_map, hmeans]
    · simp only [prob_map, hmoments]
  have hv' (v : V) : ν.condEntropy (Z v) (fun x => observeInputs (∅ : Finset I) x.1) =
      ν.entropyOf (Z (left e₀)) := by
    have ho : (fun x : (∀ i, T i) × (V → B → Bool) => observeInputs (∅ : Finset I) x.1) =
        (fun _ => fun i => (none : Option (T i))) := by funext x i; simp [observeInputs]
    rw [ho, condEntropy_const, hv, hv]
  have he' (e : E) : ν.condEntropy (fun x => (Z (left e) x,Z (right e) x))
      (fun x => observeInputs (∅ : Finset I) x.1) =
        ν.entropyOf (fun x => (Z (left e₀) x,Z (right e₀) x)) := by
    have ho : (fun x : (∀ i, T i) × (V → B → Bool) => observeInputs (∅ : Finset I) x.1) =
        (fun _ => fun i => (none : Option (T i))) := by funext x i; simp [observeInputs]
    rw [ho, condEntropy_const]
    exact he e
  have ht := symmetric_table_entropy P Y K left right reads (fun _ => ∅) (fun _ => ∅)
    hlocal charge hdegree (by intro v e hve; exact Finset.empty_subset _) hcard hv' he'
  have h := scalar_pair_overlap ν (Z (left e₀)) (Z (right e₀))
    (show (0:ℝ) < (d:ℝ)+1 by positivity) (hmeans _) (hmeans _) (by
      simpa only [add_sub_cancel_right] using ht)
  rwa [hmoments] at h

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/LocalHomogeneity.lean ===== -/

/-! Homogeneity is stated as measure-preserving input relabelings that
intertwine outputs and views. It contains no entropy or occupancy inequalities.
Every ancestor restriction inherits these actual relabeling identities. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

def endpoint {V E : Type*} (left right : E → V) (e : E) (b : Bool) : V :=
  if b then right e else left e

structure EndpointTransport {Ω V E A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (μ : FiniteProb Ω) (U : V → Ω → Option A) (W : ℕ → V → Ω → B) (F : ℕ → E → Ω → B)
    (left right : E → V) (s t : E × Bool) where
  input : Ω → Ω
  preserves : μ.map input = μ
  firstView : ℕ → B ≃ B
  secondView : ℕ → B ≃ B
  sharedView : ℕ → B ≃ B
  outputFirst : ∀ ω, U (endpoint left right t.1 t.2) (input ω) = U (endpoint left right s.1 s.2) ω
  outputSecond : ∀ ω, U (endpoint left right t.1 (!t.2)) (input ω) = U (endpoint left right s.1 (!s.2)) ω
  viewFirst : ∀ j ω, W j (endpoint left right t.1 t.2) (input ω) =
    firstView j (W j (endpoint left right s.1 s.2) ω)
  viewSecond : ∀ j ω, W j (endpoint left right t.1 (!t.2)) (input ω) =
    secondView j (W j (endpoint left right s.1 (!s.2)) ω)
  viewShared : ∀ j ω, F j t.1 (input ω) = sharedView j (F j s.1 ω)

def ViewHomogeneous {Ω V E A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (μ : FiniteProb Ω) (U : V → Ω → Option A) (W : ℕ → V → Ω → B) (F : ℕ → E → Ω → B)
    (left right : E → V) : Prop :=
  ∀ s t : E × Bool, Nonempty (EndpointTransport μ U W F left right s t)

namespace FiniteProb

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

theorem occupancyScalar_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (U U' : Ω → Option A) (Y Y' : Ω → B) (β : B ≃ B)
    (hU : ∀ ω, U' (e ω) = U ω) (hY : ∀ ω, Y' (e ω) = β (Y ω)) (D : ℝ) (ω : Ω) :
    μ.occupancyScalar U' Y' D (Y' (e ω)) = μ.occupancyScalar U Y D (Y ω) := by
  rw [hY]
  unfold occupancyScalar
  rw [← (μ.given Y' (β (Y ω))).prob_map U' (fun x => x ≠ none),
    μ.given_map_transport e he U U' Y Y' β hU hY, prob_map]

end FiniteProb

namespace ViewHomogeneous

variable {Ω V E A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    {μ : FiniteProb Ω} {U : V → Ω → Option A} {W : ℕ → V → Ω → B} {F : ℕ → E → Ω → B}
    {left right : E → V}

theorem survivor (h : ViewHomogeneous μ U W F left right) (m n : ℕ) :
    ViewHomogeneous μ (fun v => μ.survivor (U v) (fun j => W (j+1) v) m n) W F left right := by
  intro s t
  obtain ⟨a⟩ := h s t
  exact ⟨{ a with
    outputFirst := μ.survivor_transport a.input a.preserves _ _ _ _ (fun j => a.firstView (j+1))
      a.outputFirst (fun j => a.viewFirst (j+1)) m n
    outputSecond := μ.survivor_transport a.input a.preserves _ _ _ _ (fun j => a.secondView (j+1))
      a.outputSecond (fun j => a.viewSecond (j+1)) m n }⟩

theorem firstDeleted (h : ViewHomogeneous μ U W F left right) (m n : ℕ) :
    ViewHomogeneous μ (fun v => μ.firstDeleted (U v) (fun j => W (j+1) v) m n) W F left right := by
  intro s t
  obtain ⟨a⟩ := h s t
  exact ⟨{ a with
    outputFirst := μ.firstDeleted_transport a.input a.preserves _ _ _ _ (fun j => a.firstView (j+1))
      a.outputFirst (fun j => a.viewFirst (j+1)) m n
    outputSecond := μ.firstDeleted_transport a.input a.preserves _ _ _ _ (fun j => a.secondView (j+1))
      a.outputSecond (fun j => a.viewSecond (j+1)) m n }⟩

theorem scalar_pair_moment (h : ViewHomogeneous μ U W F left right) (j : ℕ) (D : ℝ)
    (e e' : E) :
    μ.expect (fun ω => μ.occupancyScalar (U (left e')) (W j (left e')) D (W j (left e') ω) *
      μ.occupancyScalar (U (right e')) (W j (right e')) D (W j (right e') ω)) =
    μ.expect (fun ω => μ.occupancyScalar (U (left e)) (W j (left e)) D (W j (left e) ω) *
      μ.occupancyScalar (U (right e)) (W j (right e)) D (W j (right e) ω)) := by
  obtain ⟨a⟩ := h (e,false) (e',false)
  rw [← μ.expect_invariant a.input a.preserves]
  apply μ.expect_congr
  intro ω
  have h1 := μ.occupancyScalar_transport a.input a.preserves _ _ _ _ (a.firstView j)
    a.outputFirst (a.viewFirst j) D ω
  have h2 := μ.occupancyScalar_transport a.input a.preserves _ _ _ _ (a.secondView j)
    a.outputSecond (a.viewSecond j) D ω
  simpa only [endpoint, Bool.not_false, Bool.false_eq_true, if_false, if_true] using congrArg₂ (·*·) h1 h2

theorem scalar_mean (h : ViewHomogeneous μ U W F left right) (j : ℕ) (D : ℝ)
    (e₀ : E) (v : V) (hcover : ∃ e b, endpoint left right e b = v) :
    μ.expect (fun ω => μ.occupancyScalar (U v) (W j v) D (W j v ω)) =
      μ.expect (fun ω => μ.occupancyScalar (U (left e₀)) (W j (left e₀)) D (W j (left e₀) ω)) := by
  obtain ⟨e,b,rfl⟩ := hcover
  obtain ⟨a⟩ := h (e₀,false) (e,b)
  rw [← μ.expect_invariant a.input a.preserves]
  apply μ.expect_congr
  intro ω
  exact μ.occupancyScalar_transport a.input a.preserves _ _ _ _ (a.firstView j)
    a.outputFirst (a.viewFirst j) D ω

theorem weighted_failure_equal (h : ViewHomogeneous μ U W F left right)
    (j : ℕ) (D : ℝ) (ell : ℕ) (v : V) (e e' : E)
    (hv : edgeIncident left right v e) (hv' : edgeIncident left right v e') :
    μ.expect (fun ω => μ.occupancyScalar (U v) (W j v) D (W j v ω) *
      bit (((μ.given (F j e') (F j e' ω)).map (U v)).tail ell <
        μ.occupancyScalar (U v) (W j v) D (W j v ω))) =
    μ.expect (fun ω => μ.occupancyScalar (U v) (W j v) D (W j v ω) *
      bit (((μ.given (F j e) (F j e ω)).map (U v)).tail ell <
        μ.occupancyScalar (U v) (W j v) D (W j v ω))) := by
  have hb : ∃ b, endpoint left right e b = v :=
    hv.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  have hb' : ∃ b, endpoint left right e' b = v :=
    hv'.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  obtain ⟨b,hb⟩ := hb
  obtain ⟨b',hb'⟩ := hb'
  obtain ⟨a⟩ := h (e,b) (e',b')
  have hu : ∀ ω, U v (a.input ω) = U v ω := by simpa only [hb, hb'] using a.outputFirst
  have hy : ∀ ω, W j v (a.input ω) = a.firstView j (W j v ω) := by
    simpa only [hb, hb'] using a.viewFirst j
  rw [← μ.expect_invariant a.input a.preserves]
  apply μ.expect_congr
  intro ω
  have hs := μ.occupancyScalar_transport a.input a.preserves (U v) (U v) (W j v) (W j v)
    (a.firstView j) hu hy D ω
  have ht := μ.given_map_transport a.input a.preserves (U v) (U v) (F j e) (F j e')
    (a.sharedView j) hu (a.viewShared j) (F j e ω)
  rw [hs, a.viewShared j ω, ht]

theorem output_distribution (h : ViewHomogeneous μ U W F left right)
    (e₀ : E) (v : V) (hcover : ∃ e b, endpoint left right e b = v) :
    μ.map (U v) = μ.map (U (left e₀)) := by
  obtain ⟨e,b,rfl⟩ := hcover
  obtain ⟨a⟩ := h (e₀,false) (e,b)
  exact μ.map_transport a.input a.preserves _ _ a.outputFirst

theorem vertex_conditional_entropy (h : ViewHomogeneous μ U W F left right)
    (j : ℕ) (e₀ : E) (v : V) (hcover : ∃ e b, endpoint left right e b = v) :
    μ.condEntropy (U v) (W j v) = μ.condEntropy (U (left e₀)) (W j (left e₀)) := by
  obtain ⟨e,b,rfl⟩ := hcover
  obtain ⟨a⟩ := h (e₀,false) (e,b)
  exact μ.conditional_entropy_transport a.input a.preserves _ _ _ _ (Equiv.refl _) (a.firstView j)
    a.outputFirst (a.viewFirst j)

theorem edge_conditional_entropy (h : ViewHomogeneous μ U W F left right)
    (j : ℕ) (e₀ e : E) :
    μ.condEntropy (fun ω => (U (left e) ω,U (right e) ω)) (F j e) =
      μ.condEntropy (fun ω => (U (left e₀) ω,U (right e₀) ω)) (F j e₀) := by
  obtain ⟨a⟩ := h (e₀,false) (e,false)
  exact μ.conditional_entropy_transport a.input a.preserves _ _ _ _ (Equiv.refl _) (a.sharedView j)
    (fun ω => Prod.ext (a.outputFirst ω) (a.outputSecond ω)) (a.viewShared j)

end ViewHomogeneous
end
end MISLocal


/- ===== Source: MISLocal/InputGeometry.lean ===== -/

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


/- ===== Source: MISLocal/GeometricTruncation.lean ===== -/

/-! The robust truncation estimate on an explicit independent-source
geometry. The scalar, branch and tail estimates are all derived here; none
is assumed as a probability-inequality premise. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem geometric_truncation {I V E A : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]
    {T : I → Type} [∀ i, Fintype (T i)] {d r : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d r)
    (U : V → (∀ i, T i) → Option A)
    (hhom : ViewHomogeneous (pi P) U g.vertexObservation g.sharedObservation g.left g.right)
    (j : ℕ) (hj : j < r) (e₀ : E) (ell M m : ℕ)
    (hD : 12 ≤ (d:ℝ)+1) (hlog : 1 ≤ Real.log ((d:ℝ)+1))
    (hell : 0 < ell) (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*((d:ℝ)+1) ≤ ((d:ℝ)+1)^4)
    (hratio : (M:ℝ)/m = 1/((d:ℝ)+1))
    (hatom : ∀ v b, 0 < ((pi P).map (g.vertexObservation (j+1) v)).weight b → ∀ a,
      (((pi P).given (g.vertexObservation (j+1) v) b).map (U v)).weight (some a) ≤ 1/(m:ℝ))
    (G : (∀ i, Option (T i)) → A × A → Bool) {q : ℝ}
    (hbad : (pi P).prob (fun ω => exceptionalMatrix ell (G (g.sharedObservation (j+1) e₀ ω))) ≤ q)
    (hq : q ≤ 1/((d:ℝ)+1)^2) :
    (pi P).prob (fun ω => U (g.left e₀) ω ≠ none) ≤
      2100*Real.log ((d:ℝ)+1)/((d:ℝ)+1) +
        6*Real.sqrt ((pi P).kernelConflict
          (fun ω => ((pi P).given (g.vertexObservation j (g.left e₀)) (g.vertexObservation j (g.left e₀) ω)).map (U (g.left e₀)))
          (fun ω => ((pi P).given (g.vertexObservation j (g.right e₀)) (g.vertexObservation j (g.right e₀) ω)).map (U (g.right e₀)))
          (fun ω => G (g.sharedObservation (j+1) e₀ ω))) := by
  let μ := pi P
  let D : ℝ := (d:ℝ)+1
  let W := g.vertexObservation (T := T)
  let F := g.sharedObservation (T := T)
  let f := fun v => μ.occupancyScalar (U v) (W (j+1) v) D
  let p := μ.expect (fun ω => f (g.left e₀) (W (j+1) (g.left e₀) ω))
  have hDp : 0 < D := by dsimp [D]; positivity
  have hmean (v : V) : μ.expect (fun ω => f v (W (j+1) v ω)) = p :=
    hhom.scalar_mean (j+1) D e₀ v (g.endpoint_cover v)
  have hscalar := scalar_overlap_from_sources P (W (j+1)) f
    (fun v b => μ.occupancyScalar_nonneg (U v) (W (j+1) v) D b)
    (fun v b => μ.occupancyScalar_le_one (U v) (W (j+1) v) hDp b)
    g.left g.right g.readers
    (fun v => observeInputs_readsOnly _ _ (g.vertex_readers (j+1) v (by omega)))
    g.unconditionedCharge g.degree g.edgeCount g.noLoop e₀ hmean
    (fun e => hhom.scalar_pair_moment (j+1) D e₀ e)
  have hfailure (v : V) (hve : edgeIncident g.left g.right v e₀) :
      μ.expect (fun ω => f v (W (j+1) v ω) *
        bit (((μ.given (F (j+1) e₀) (F (j+1) e₀ ω)).map (U v)).tail ell < f v (W (j+1) v ω))) ≤
          (256*Real.log D/D)*p := by
    have hc : Fintype.card {e // edgeIncident g.left g.right v e} = d+1 := by
      rw [Fintype.card_subtype, g.degree]
    have href (e : {e // edgeIncident g.left g.right v e}) (ω : ∀ i, T i) :
        W (j+1) v ω = restrictObservation (g.vertex (j+1) v) (F (j+1) e.val ω) :=
      g.vertex_from_shared (j+1) (by omega) v e.val e.property ω
    have hh := μ.weighted_branch_at (U v) (W (j+1) v)
      (fun e : {e // edgeIncident g.left g.right v e} => F (j+1) e.val)
      (fun _ => restrictObservation (g.vertex (j+1) v)) href ell M m
      (by simpa only [hc, Nat.cast_add, Nat.cast_one] using hD)
      (by simpa only [hc, Nat.cast_add, Nat.cast_one] using hlog) hM hm hellM
      (by simpa only [hc, Nat.cast_add, Nat.cast_one] using hsize)
      (by simpa only [hc, Nat.cast_add, Nat.cast_one] using hratio)
      (g.branch_views_independent P (j+1) (by omega) v) (hatom v) ⟨e₀,hve⟩
      (fun e => by
        simpa only [hc, Nat.cast_add, Nat.cast_one] using
          hhom.weighted_failure_equal (j+1) D ell v e₀ e.val hve e.property)
    have hh' : μ.expect (fun ω => f v (W (j+1) v ω) *
        bit (((μ.given (F (j+1) e₀) (F (j+1) e₀ ω)).map (U v)).tail ell < f v (W (j+1) v ω))) ≤
          (256*Real.log D/D)*μ.expect (fun ω => f v (W (j+1) v ω)) := by
      simpa only [hc, Nat.cast_add, Nat.cast_one] using hh
    rwa [hmean] at hh'
  have htail := μ.projected_endpoint_tails (U (g.left e₀)) (U (g.right e₀))
    (W j (g.left e₀)) (W j (g.right e₀)) (F (j+1) e₀)
    (restrictObservation (g.shared (j+1) e₀)) (restrictObservation (g.shared (j+1) e₀))
    (g.next_shared_from_vertex j hj (g.left e₀) e₀ (Or.inl rfl))
    (g.next_shared_from_vertex j hj (g.right e₀) e₀ (Or.inr rfl))
    (g.endpoint_views_independent P j hj e₀) G hell hbad
  exact μ.truncation_from_local_moments (U (g.left e₀)) (W (j+1) (g.left e₀))
    (fun ω => f (g.right e₀) (W (j+1) (g.right e₀) ω))
    (fun ω => ((μ.given (F (j+1) e₀) (F (j+1) e₀ ω)).map (U (g.left e₀))).tail ell)
    (fun ω => ((μ.given (F (j+1) e₀) (F (j+1) e₀ ω)).map (U (g.right e₀))).tail ell)
    hDp hlog (μ.kernelConflict_nonneg _ _ _) hq
    (fun ω => μ.occupancyScalar_nonneg _ _ _ _)
    (fun ω => μ.occupancyScalar_le_one _ _ hDp _)
    (fun ω => listTail_nonneg _ _) (fun ω => listTail_nonneg _ _) htail
    (hfailure (g.left e₀) (Or.inl rfl)) (hfailure (g.right e₀) (Or.inr rfl)) hscalar

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/HomogeneousEntropy.lean ===== -/

/-! The conditional entropy inequality for a homogeneous local output field,
derived from its independent sources and combinatorial routing geometry. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem homogeneous_conditional_entropy {I V E A : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Nonempty V] [Fintype E] [Fintype A]
    {T : I → Type*} [∀ i, Fintype (T i)] {d r : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d r)
    (U : V → (∀ i, T i) → Option A)
    (hlocal : ∀ v, ReadsOnly (U v) (g.readers v))
    (hhom : ViewHomogeneous (pi P) U g.vertexObservation g.sharedObservation g.left g.right)
    (j : ℕ) (hj : j ≤ r) (e₀ : E) :
    (((d:ℝ)+1)/2)*(pi P).condEntropy (fun ω => (U (g.left e₀) ω,U (g.right e₀) ω))
      (g.sharedObservation j e₀) ≥
        (d:ℝ)*(pi P).condEntropy (U (g.left e₀)) (g.vertexObservation j (g.left e₀)) := by
  exact symmetric_conditional_entropy_finite P U g.left g.right g.readers (g.vertex j) (g.shared j)
    hlocal (g.charge j hj) g.edgeCount
    (fun v => hhom.vertex_conditional_entropy j e₀ v (g.endpoint_cover v))
    (fun e => hhom.edge_conditional_entropy j e₀ e)

theorem keptOutput_readsOnly {I A B : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A] [Fintype B]
    (μ : FiniteProb (∀ i, T i)) (U : (∀ i, T i) → Option A) (Y : (∀ i, T i) → B)
    (m : ℕ) (R : Finset I) (hU : ReadsOnly U R) (hY : ReadsOnly Y R) :
    ReadsOnly (μ.keptOutput U Y m) R := by
  intro x z hxz
  simp only [keptOutput, hU x z hxz, hY x z hxz]

theorem deletedOutput_readsOnly {I A B : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A] [Fintype B]
    (μ : FiniteProb (∀ i, T i)) (U : (∀ i, T i) → Option A) (Y : (∀ i, T i) → B)
    (m : ℕ) (R : Finset I) (hU : ReadsOnly U R) (hY : ReadsOnly Y R) :
    ReadsOnly (μ.deletedOutput U Y m) R := by
  intro x z hxz
  simp only [deletedOutput, hU x z hxz, hY x z hxz]

theorem survivor_readsOnly {I A B : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A] [Fintype B]
    (μ : FiniteProb (∀ i, T i)) (U : (∀ i, T i) → Option A) (Y : ℕ → (∀ i, T i) → B)
    (m n : ℕ) (R : Finset I) (hU : ReadsOnly U R) (hY : ∀ j, j < n → ReadsOnly (Y j) R) :
    ReadsOnly (μ.survivor U Y m n) R := by
  induction n with
  | zero => exact hU
  | succ n ih =>
    exact μ.keptOutput_readsOnly _ _ m R (ih (fun j hj => hY j (by omega))) (hY n (by omega))

theorem firstDeleted_readsOnly {I A B : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A] [Fintype B]
    (μ : FiniteProb (∀ i, T i)) (U : (∀ i, T i) → Option A) (Y : ℕ → (∀ i, T i) → B)
    (m n : ℕ) (R : Finset I) (hU : ReadsOnly U R) (hY : ∀ j, j ≤ n → ReadsOnly (Y j) R) :
    ReadsOnly (μ.firstDeleted U Y m n) R :=
  μ.deletedOutput_readsOnly _ _ m R
    (μ.survivor_readsOnly U Y m n R hU (fun j hj => hY j hj.le)) (hY n (le_refl n))

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/ConditionalReadLocality.lean ===== -/

/-! Additional observed coordinates do not change a local output's
conditional distribution when every newly observed coordinate lies outside
its read set. The proof uses actual conditional product independence. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem conditional_product_disjoint_reads {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] (P : ∀ i, FiniteProb (T i))
    (f h : (∀ i, T i) → ℝ) (R S L : Finset I)
    (hf : ReadsOnly f R) (hh : ReadsOnly h S) (hinter : R ∩ S ⊆ L)
    (y : ∀ i, Option (T i)) (hy : 0 < ((pi P).map (observeInputs L)).weight y) :
    ((pi P).given (observeInputs L) y).expect (fun x => f x*h x) =
      ((pi P).given (observeInputs L) y).expect f * ((pi P).given (observeInputs L) y).expect h := by
  have hind := conditional_independent_of_disjoint_reads P
    (fun b : Bool => if b then h else f) (fun b : Bool => if b then S else R) L
    (by intro b; cases b <;> assumption)
    (by
      intro b c hbc i hi hi'
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · exact hinter (Finset.mem_inter.mpr ⟨hi,hi'⟩)
      · exact hinter (Finset.mem_inter.mpr ⟨hi',hi⟩)
      · exact False.elim (hbc rfl)) y hy
  simpa only [Bool.false_eq_true, if_false, if_true, id_eq] using hind.bool_product id id

theorem conditional_reads_irrelevance {I A : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A]
    (P : ∀ i, FiniteProb (T i)) (U : (∀ i, T i) → A) (R S L : Finset I)
    (hU : ReadsOnly U R) (hSL : S ⊆ L) (hinter : R ∩ L ⊆ S)
    (ω : ∀ i, T i) (hω : 0 < (pi P).weight ω) :
    (((pi P).given (observeInputs L) (observeInputs L ω)).map U) =
      (((pi P).given (observeInputs S) (observeInputs S ω)).map U) := by
  let μ := pi P
  let F := observeInputs (T := T) L
  let Y := observeInputs (T := T) S
  have href (x : ∀ i, T i) : Y x = restrictObservation S (F x) :=
    (restrictObservation_observe S L hSL x).symm
  have hF := μ.map_weight_pos F hω
  have hY := μ.map_weight_pos Y hω
  have hc : 0 < ((μ.given Y (Y ω)).map F).weight (F ω) := by
    have he := μ.given_refinement_mass F Y (restrictObservation S) href (F ω)
      (by rwa [← href ω])
    rw [← href ω] at he
    rw [he]
    exact div_pos hF hY
  have hn := μ.given_given_refinement F Y (restrictObservation S) href (F ω) hF
  rw [← href ω] at hn
  rw [← hn]
  ext a
  rw [given_pair_mass _ U F a (F ω) hc]
  have hprod := conditional_product_disjoint_reads P (fun x => bit (U x=a)) (fun x => bit (F x=F ω))
    R L S (by intro x z hxz; exact congrArg (fun u => bit (u=a)) (hU x z hxz))
    (by
      intro x z hxz
      exact congrArg (fun u => bit (u=F ω))
        ((observeInputs_readsOnly L L (Finset.Subset.refl L)) x z hxz))
    hinter (Y ω) hY
  have heq : ((μ.given Y (Y ω)).map (fun x => (U x,F x))).weight (a,F ω) =
      ((μ.given Y (Y ω)).map U).weight a * ((μ.given Y (Y ω)).map F).weight (F ω) := by
    change (μ.given Y (Y ω)).expect (fun x => bit ((U x,F x)=(a,F ω))) = _
    rw [expect_congr _ (fun x => show bit ((U x,F x)=(a,F ω)) = bit (U x=a)*bit (F x=F ω) from by
      by_cases hu : U x=a <;> by_cases hf : F x=F ω <;> simp [bit, Prod.mk.injEq, hu, hf])]
    exact hprod
  rw [heq, mul_div_cancel_right₀ _ (ne_of_gt hc)]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/ProjectionConflict.lean ===== -/

/-! Exact conflict identities for direct projection, its initial layer,
and its final empty-view layer. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

theorem projectedPair_conflict_eq (μ : FiniteProb Ω) (U V : Ω → Option A)
    (F : Ω → C) (y z : C → B) (G : C → A × A → Bool) :
    (μ.projectedPair F U V y z).prob (selectedConflict (fun c a b => G c (a,b)=true)) =
      μ.kernelConflict (fun ω => (μ.given (fun x => y (F x)) (y (F ω))).map U)
        (fun ω => (μ.given (fun x => z (F x)) (z (F ω))).map V) (fun ω => G (F ω)) := by
  let f := fun c => ∑ a, ∑ b, ((μ.given (fun x => y (F x)) (y c)).map U).weight (some a) *
    ((μ.given (fun x => z (F x)) (z c)).map V).weight (some b)*bit (G c (a,b)=true)
  change _ = μ.expect (fun ω => f (F ω))
  rw [← μ.expect_map F f]
  simp only [prob, expect, projectedPair, Fintype.sum_prod_type, Fintype.sum_option,
    selectedConflict, bit_false, mul_zero, Finset.sum_const_zero, zero_add, f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem given_const (μ : FiniteProb Ω) (c b : B) : μ.given (fun _ => c) b = μ := by
  by_cases h : c=b
  · subst b
    have hp : (μ.map (fun _ => c)).weight c = 1 := by simp [map]
    ext ω
    rw [given_weight _ _ c (by rw [hp]; norm_num), hp]
    simp [bit]
  · have hz : (μ.map (fun _ => c)).weight b = 0 := by simp [map, h]
    simp only [given, hz, lt_self_iff_false, dif_neg, not_false_eq_true]

theorem given_empty_observation {I : Type*} [DecidableEq I] {T : I → Type*}
    [Fintype I] [∀ i, Fintype (T i)] (P : FiniteProb (∀ i, T i)) (b : ∀ i, Option (T i)) :
    P.given (observeInputs ∅) b = P := by
  have he : observeInputs (T := T) ∅ = fun _ => fun i => (none : Option (T i)) := by
    funext x i
    simp [observeInputs]
  rw [he, given_const]

theorem kernelConflict_constant (μ : FiniteProb Ω) (P Q : FiniteProb (Option A))
    (G : Ω → A × A → Bool) {c : ℝ} (hfair : ∀ a b, μ.prob (fun ω => G ω (a,b)=true) = c) :
    μ.kernelConflict (fun _ => P) (fun _ => Q) G =
      P.prob (fun a => a ≠ none)*Q.prob (fun a => a ≠ none)*c := by
  have hf (a b : A) : μ.expect (fun ω => bit (G ω (a,b)=true)) = c := hfair a b
  simp only [kernelConflict, expect_sum, expect_mul, hf, ← Finset.mul_sum, ← Finset.sum_mul,
    occupied_mass]

omit [Fintype A] [Fintype C] in
theorem zero_conflict_of_restrictions (μ : FiniteProb Ω) (U V U' V' : Ω → Option A)
    (F : Ω → C) (E : C → A → A → Prop)
    (hU : ∀ ω a, U' ω=some a → U ω=some a) (hV : ∀ ω a, V' ω=some a → V ω=some a)
    (hz : μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) = 0) :
    μ.prob (fun ω => selectedConflict E (F ω,U' ω,V' ω)) = 0 := by
  apply le_antisymm _ (μ.prob_nonneg _)
  calc
    _ ≤ μ.prob (fun ω => selectedConflict E (F ω,U ω,V ω)) := μ.prob_mono (fun ω =>
      selectedConflict_of_restriction E _ _ _ _ _ (hU ω) (hV ω))
    _ = 0 := hz

theorem initial_projection_conflict {I V E : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Fintype E]
    {T : I → Type*} [∀ i, Fintype (T i)] {d r : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d r)
    (U : V → (∀ i, T i) → Option A) (hlocal : ∀ v, ReadsOnly (U v) (g.readers v))
    (e : E) (G : (∀ i, Option (T i)) → A × A → Bool) :
    (pi P).kernelConflict
      (fun ω => (((pi P).given (g.vertexObservation 0 (g.left e)) (g.vertexObservation 0 (g.left e) ω)).map (U (g.left e))))
      (fun ω => (((pi P).given (g.vertexObservation 0 (g.right e)) (g.vertexObservation 0 (g.right e) ω)).map (U (g.right e))))
      (fun ω => G (g.sharedObservation 0 e ω)) =
        (pi P).prob (fun ω => selectedConflict (fun b a a' => G b (a,a')=true)
          (g.sharedObservation 0 e ω,U (g.left e) ω,U (g.right e) ω)) := by
  let μ := pi P
  let F := g.sharedObservation (T := T) 0 e
  let conflict := fun ω => selectedConflict (fun b a a' => G b (a,a')=true)
    (F ω,U (g.left e) ω,U (g.right e) ω)
  have hind (b) (hb : 0 < (μ.map F).weight b) :
      (μ.given F b).map (fun ω => (U (g.left e) ω,U (g.right e) ω)) =
        ((μ.given F b).map (U (g.left e))).product ((μ.given F b).map (U (g.right e))) := by
    apply independent_bool_pair_distribution _ (fun b : Bool => if b then U (g.right e) else U (g.left e))
    apply conditional_independent_of_disjoint_reads P _
      (fun b : Bool => if b then g.readers (g.right e) else g.readers (g.left e)) (g.shared 0 e)
      (by intro b; cases b <;> exact hlocal _) _ b hb
    intro s t hst i hi hi'
    cases s <;> cases t
    · exact False.elim (hst rfl)
    · exact g.initial_reader_overlap e (Finset.mem_inter.mpr ⟨hi,hi'⟩)
    · exact g.initial_reader_overlap e (Finset.mem_inter.mpr ⟨hi',hi⟩)
    · exact False.elim (hst rfl)
  have hk (v) (hv : edgeIncident g.left g.right v e) (ω) (hω : 0 < μ.weight ω) :
      ((μ.given (g.vertexObservation 0 v) (g.vertexObservation 0 v ω)).map (U v)) =
        ((μ.given F (F ω)).map (U v)) := by
    exact (conditional_reads_irrelevance P (U v) (g.readers v) (g.vertex 0 v) (g.shared 0 e)
      (hlocal v) (g.contains 0 v e (Nat.zero_le r) hv) (g.initial_shared_overlap v e hv) ω hω).symm
  change μ.expect _ = μ.prob conflict
  have he : μ.expect (fun ω => (μ.given F (F ω)).prob conflict) = μ.prob conflict := by
    rw [← μ.expect_map F (fun b => (μ.given F b).prob conflict)]
    exact μ.total_conditional_expectation F (fun ω => bit (conflict ω))
  rw [← he]
  apply μ.expect_congr_on_support
  intro ω hω
  dsimp only
  rw [hk _ (Or.inl rfl) ω hω, hk _ (Or.inr rfl) ω hω]
  rw [← product_selected_probability, ← hind (F ω) (μ.map_weight_pos F hω), prob_map]
  symm
  apply μ.given_prob_congr F (F ω) (μ.map_weight_pos F hω)
  intro x hx
  simp only [conflict, hx, selectedConflict]
  rfl

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/GeometricBudget.lean ===== -/

/-! Direct-projection conflict charging for a homogeneous local field with
short conditional support. The entropy inequality is derived, not assumed. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem geometric_projection_budget {I V E A : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Nonempty V] [Fintype E] [Fintype A]
    {T : I → Type*} [∀ i, Fintype (T i)] {d r : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d r)
    (U : V → (∀ i, T i) → Option A)
    (hlocal : ∀ v, ReadsOnly (U v) (g.readers v))
    (hhom : ViewHomogeneous (pi P) U g.vertexObservation g.sharedObservation g.left g.right)
    (j : ℕ) (hj : j ≤ r) (e₀ : E) (S : (∀ i, Option (T i)) → Finset A) {m : ℝ}
    (hm : 0 < m) (hcard : ∀ b, ((S b).card:ℝ) ≤ m)
    (hsupport : ∀ b, 0 < ((pi P).map (g.vertexObservation j (g.left e₀))).weight b → ∀ a,
      a ∉ S b → (((pi P).given (g.vertexObservation j (g.left e₀)) b).map (U (g.left e₀))).weight (some a)=0)
    (G : (∀ i, Option (T i)) → A × A → Bool)
    (hzero : (pi P).prob (fun ω => selectedConflict (fun b a a' => G b (a,a')=true)
      (g.sharedObservation j e₀ ω,U (g.left e₀) ω,U (g.right e₀) ω)) = 0) :
    (pi P).kernelConflict
      (fun ω => (((pi P).given (g.vertexObservation j (g.left e₀)) (g.vertexObservation j (g.left e₀) ω)).map (U (g.left e₀))))
      (fun ω => (((pi P).given (g.vertexObservation j (g.right e₀)) (g.vertexObservation j (g.right e₀) ω)).map (U (g.right e₀))))
      (fun ω => G (g.sharedObservation j e₀ ω)) ≤
        2*massBudget m ((pi P).prob (fun ω => U (g.left e₀) ω ≠ none))/((d:ℝ)+1) := by
  let μ := pi P
  let F := g.sharedObservation (T := T) j e₀
  let y := restrictObservation (T := T) (g.vertex j (g.left e₀))
  let z := restrictObservation (T := T) (g.vertex j (g.right e₀))
  have hy (ω : ∀ i, T i) : y (F ω) = g.vertexObservation j (g.left e₀) ω :=
    (g.vertex_from_shared j hj (g.left e₀) e₀ (Or.inl rfl) ω).symm
  have hz (ω : ∀ i, T i) : z (F ω) = g.vertexObservation j (g.right e₀) ω :=
    (g.vertex_from_shared j hj (g.right e₀) e₀ (Or.inr rfl) ω).symm
  have h := μ.direct_projection_rare_bound F (U (g.left e₀)) (U (g.right e₀)) y z S
    (selectedConflict (fun b a a' => G b (a,a')=true))
    (D := (d:ℝ)+1) (K := 0) (by positivity) hm (le_refl 0) hcard
    (by simpa only [hy] using hsupport)
    (by simpa only [hy, hz] using hhom.vertex_conditional_entropy j e₀ (g.right e₀) (g.endpoint_cover _))
    (by
      have he := homogeneous_conditional_entropy P g U hlocal hhom j hj e₀
      simpa only [hy, hz, add_sub_cancel_right, add_zero] using he)
    (by rwa [prob_map])
  rw [projectedPair_conflict_eq] at h
  simpa only [hy, hz] using h

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/FiniteOccupancy.lean ===== -/

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


/- ===== Source: MISLocal/GraphBalls.lean ===== -/

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


/- ===== Source: MISLocal/GraphInputGeometry.lean ===== -/

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


/- ===== Source: MISLocal/PrivateGeometry.lean ===== -/

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


/- ===== Source: MISLocal/GraphOccupancy.lean ===== -/

/-! The concrete graph occupancy theorem. Inputs are independent fair
Boolean matrices on actual edges, together with independent finite private
randomness at each vertex. The round views and their geometric properties
are constructed from the graph, rather than supplied as a certificate.

Symmetry is the explicit input/output relabeling condition `ViewHomogeneous`.
There are no assumed entropy, support, truncation, or occupancy estimates.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

namespace FiniteProb

theorem pi_map_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] (P : ∀ i, FiniteProb (T i)) (i : I) :
    (pi P).map (fun x => x i) = P i := by
  ext a
  change (pi P).expect (fun x => bit (x i = a)) = _
  rw [pi_expect_coordinate P i (fun b => bit (b=a))]
  simp [expect, bit]

end FiniteProb

namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev matrixPrivateType (k : ℕ) (Q : V → Type) : G.edgeSet ⊕ V → Type :=
  Sum.elim (fun _ => Fin k × Fin k → Bool) Q

def matrixPrivateProbability (k : ℕ) {Q : V → Type} [∀ v, Fintype (Q v)]
    (R : ∀ v, FiniteProb (Q v)) :
    ∀ i, FiniteProb (matrixPrivateType G k Q i) :=
  FiniteProb.sumProb (fun _ => FiniteProb.fairBits (Fin k × Fin k)) R

/-- Occupancy of an `(n+1)`-round homogeneous independent-set rule, with
private vertex randomness. The local-tree hypothesis refers to finite
neighborhoods only: the whole regular graph is not assumed to be a tree. -/
theorem graph_occupancy {d n k : ℕ}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    {Q : V → Type} [∀ v, Fintype (Q v)] (R : ∀ v, FiniteProb (Q v))
    (U : V → (∀ i, matrixPrivateType G k Q i) → Option (Fin k))
    (hlocal : ∀ v, ReadsOnly (U v) (privateReads (seen G (n+1)) v))
    (hhom : ViewHomogeneous (FiniteProb.pi (matrixPrivateProbability G k R)) U
      (fun j v => observeInputs (rawView (V := V) (seen G (n+1-j) v)))
      (fun j e => observeInputs (rawView (V := V) (sharedEdges G (n+1-j) e)))
      (edgeLeft G) (edgeRight G))
    (e₀ : G.edgeSet)
    (hzero : (FiniteProb.pi (matrixPrivateProbability G k R)).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),U (edgeLeft G e₀) ω,U (edgeRight G e₀) ω)) = 0)
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G k R)).prob
      (fun ω => U (edgeLeft G e₀) ω ≠ none) ≤ occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  let g := (graphInputGeometry G d n hreg ht).withPrivate
  let P := matrixPrivateProbability G k R
  let decode := fun (_ : ℕ) (y : ∀ i, Option (matrixPrivateType G k Q i)) =>
    (y (Sum.inl e₀)).getD (fun _ => false)
  have hd (j : ℕ) (_ : j ≤ n+1) (ω : ∀ i, matrixPrivateType G k Q i) :
      decode j (g.sharedObservation j e₀ ω) = ω (Sum.inl e₀) := by
    have he : e₀ ∈ sharedEdges G (n+1-j) e₀ := Finset.mem_insert_self _ _
    simp only [decode, g, ProductInputGeometry.sharedObservation,
      ProductInputGeometry.withPrivate, graphInputGeometry, observeInputs,
      rawView, Finset.mem_map, Function.Embedding.inl_apply, Sum.inl.injEq,
      exists_eq_right, he, if_true, Option.getD_some]
  exact FiniteProb.finite_occupancy P g U hlocal hhom e₀ (fun ω => ω (Sum.inl e₀))
    decode hd (FiniteProb.pi_map_coordinate P (Sum.inl e₀)) hzero hD hk hlower hupper

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/InputRelabeling.lean ===== -/

/-! A concrete sufficient condition for view homogeneity: permute independent
source coordinates and relabel each finite source alphabet. Preservation of
the product distribution and commutation with observed views are proved, so
neither must be supplied as a probabilistic assumption. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section

structure InputRelabeling {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] (P : ∀ i, FiniteProb (T i)) where
  coordinate : I ≃ I
  value : ∀ i, T i ≃ T (coordinate i)
  weight : ∀ i a, (P (coordinate i)).weight (value i a) = (P i).weight a

namespace InputRelabeling

variable {I : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] {P : ∀ i, FiniteProb (T i)}
    (a : InputRelabeling P)

def input : (∀ i, T i) ≃ (∀ i, T i) := a.coordinate.piCongr a.value

def observation : (∀ i, Option (T i)) ≃ (∀ i, Option (T i)) :=
  a.coordinate.piCongr (fun i => Equiv.optionCongr (a.value i))

theorem preserves : (FiniteProb.pi P).map a.input = FiniteProb.pi P := by
  ext x
  rw [FiniteProb.map_equiv_weight]
  change (∏ i, (P i).weight (a.input.symm x i)) = ∏ i, (P i).weight (x i)
  calc
    _ = ∏ i, (P (a.coordinate i)).weight (x (a.coordinate i)) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [input, Equiv.piCongr_symm_apply]
      exact (a.weight i ((a.value i).symm (x (a.coordinate i)))).symm.trans
        (congrArg (P (a.coordinate i)).weight ((a.value i).apply_symm_apply _))
    _ = _ := a.coordinate.prod_comp (fun i => (P i).weight (x i))

theorem observe (S R : Finset I) (h : ∀ i, a.coordinate i ∈ R ↔ i ∈ S)
    (x : ∀ i, T i) : observeInputs R (a.input x) = a.observation (observeInputs S x) := by
  funext j
  obtain ⟨i,rfl⟩ := a.coordinate.surjective j
  simp only [input, observation, Equiv.piCongr_apply_apply, observeInputs, h i]
  by_cases hi : i ∈ S <;> simp [hi]

end InputRelabeling

/-- Ordinary coordinate relabelings suffice for all the distributional
symmetry used in the occupancy argument. Only the algorithm's pointwise
equivariance and the relabeling of its coordinate views remain premises. -/
theorem viewHomogeneous_of_input_relabelings {I V E A : Type*}
    [Fintype I] [DecidableEq I] [Fintype A]
    {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (U : V → (∀ i, T i) → Option A)
    (W : ℕ → V → Finset I) (F : ℕ → E → Finset I) (left right : E → V)
    (a : (E × Bool) → (E × Bool) → InputRelabeling P)
    (hu : ∀ s t ω, U (endpoint left right t.1 t.2) ((a s t).input ω) =
      U (endpoint left right s.1 s.2) ω)
    (hu' : ∀ s t ω, U (endpoint left right t.1 (!t.2)) ((a s t).input ω) =
      U (endpoint left right s.1 (!s.2)) ω)
    (hw : ∀ s t j i, (a s t).coordinate i ∈ W j (endpoint left right t.1 t.2) ↔
      i ∈ W j (endpoint left right s.1 s.2))
    (hw' : ∀ s t j i, (a s t).coordinate i ∈ W j (endpoint left right t.1 (!t.2)) ↔
      i ∈ W j (endpoint left right s.1 (!s.2)))
    (hf : ∀ s t j i, (a s t).coordinate i ∈ F j t.1 ↔ i ∈ F j s.1) :
    ViewHomogeneous (FiniteProb.pi P) U (fun j v => observeInputs (W j v))
      (fun j e => observeInputs (F j e)) left right := by
  intro s t
  exact ⟨{
    input := (a s t).input
    preserves := (a s t).preserves
    firstView := fun _ => (a s t).observation
    secondView := fun _ => (a s t).observation
    sharedView := fun _ => (a s t).observation
    outputFirst := hu s t
    outputSecond := hu' s t
    viewFirst := fun j ω => (a s t).observe _ _ (hw s t j) ω
    viewSecond := fun j ω => (a s t).observe _ _ (hw' s t j) ω
    viewShared := fun j ω => (a s t).observe _ _ (hf s t j) ω }⟩

end
end MISLocal


/- ===== Source: MISLocal/GraphTapeReduction.lean ===== -/

/-! The fixed-tape/averaging step now uses the proved graph occupancy theorem
as a black box. Tape spaces can be infinite. No per-fixed-tape occupancy bound
is assumed. The LOCAL simulation, collision and domination interfaces remain
explicit; this module is not an unconditional asymptotic LOCAL lower bound. -/

open MeasureTheory

namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V W : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [MeasurableSpace W]
    {d n k : ℕ} {Q : V → Type} [∀ v, Fintype (Q v)]

/-- Averaging over arbitrary tape tables costs nothing in the occupancy
bound. Independence is required of the graph/private inputs, not of the
derived outputs or of neighboring execution events. -/
theorem averaged_graph_occupancy
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    (R : ∀ v, FiniteProb (Q v)) (ν : Measure W) [IsProbabilityMeasure ν]
    (U : W → V → (∀ i, matrixPrivateType G k Q i) → Option (Fin k))
    (hlocal : ∀ w v, ReadsOnly (U w v) (privateReads (seen G (n+1)) v))
    (hhom : ∀ w, ViewHomogeneous (FiniteProb.pi (matrixPrivateProbability G k R)) (U w)
      (fun j v => observeInputs (rawView (V := V) (seen G (n+1-j) v)))
      (fun j e => observeInputs (rawView (V := V) (sharedEdges G (n+1-j) e)))
      (edgeLeft G) (edgeRight G))
    (e₀ : G.edgeSet)
    (hzero : ∀ w, (FiniteProb.pi (matrixPrivateProbability G k R)).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),U w (edgeLeft G e₀) ω,U w (edgeRight G e₀) ω)) = 0)
    (hmeas : ∀ ω, MeasurableSet {w | U w (edgeLeft G e₀) ω ≠ none})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G k R)).expect
      (fun ω => ν.real {w | U w (edgeLeft G e₀) ω ≠ none}) ≤
        occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  exact average_fixed_tape_bound _ ν _ hmeas _ (fun w =>
    graph_occupancy G hreg ht R (U w) (hlocal w) (hhom w) e₀ (hzero w) hD hk hlower hupper)

/-- A finite LOCAL obstruction with the old `hfixed` occupancy premise
removed. Instead, the candidate process is represented by actual local,
homogeneous, zero-conflict label outputs, to which `graph_occupancy` applies.
Simulation and its error estimates still have to be proved for the chosen
blow-up construction. -/
theorem graph_finite_obstruction {X : Type*}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    (R : ∀ v, FiniteProb (Q v)) (ν : Measure W) [IsProbabilityMeasure ν]
    (H : (∀ i, matrixPrivateType G k Q i) → SimpleGraph X) (C : Set X)
    (output candidates : (∀ i, matrixPrivateType G k Q i) → W → Set X)
    (uniqueIDs : (∀ i, matrixPrivateType G k Q i) → Prop)
    (U : W → V → (∀ i, matrixPrivateType G k Q i) → Option (Fin k))
    (hlocal : ∀ w v, ReadsOnly (U w v) (privateReads (seen G (n+1)) v))
    (hhom : ∀ w, ViewHomogeneous (FiniteProb.pi (matrixPrivateProbability G k R)) (U w)
      (fun j v => observeInputs (rawView (V := V) (seen G (n+1-j) v)))
      (fun j e => observeInputs (rawView (V := V) (sharedEdges G (n+1-j) e)))
      (edgeLeft G) (edgeRight G))
    (e₀ : G.edgeSet)
    (hzero : ∀ w, (FiniteProb.pi (matrixPrivateProbability G k R)).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),U w (edgeLeft G e₀) ω,U w (edgeRight G e₀) ω)) = 0)
    (hrep : ∀ ω w, Occupies C (repair (H ω) (candidates ω w)) ↔ U w (edgeLeft G e₀) ω ≠ none)
    (ε δ γ : ℝ) (hε : ε ≤ 1)
    (hcollision : (FiniteProb.pi (matrixPrivateProbability G k R)).prob (fun ω => ¬uniqueIDs ω) ≤ δ)
    (hdomination : (FiniteProb.pi (matrixPrivateProbability G k R)).prob
      (fun ω => ExternallyDominatable (H ω) C) ≤ γ)
    (hcorrect : ∀ ω, 1-ε ≤ ν.real {w | Maximal (H ω).IsIndepSet (output ω w)})
    (hsimulation : ∀ ω, uniqueIDs ω → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (H ω).Adj v x → (x ∈ candidates ω w ↔ x ∈ output ω w))
    (hmeas : ∀ ω, MeasurableSet {w | Occupies C (repair (H ω) (candidates ω w))})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (1-ε)*(1-δ-γ) ≤ occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  apply finite_obstruction (FiniteProb.pi (matrixPrivateProbability G k R)) ν H C output
    candidates uniqueIDs ε δ γ _ hε hcollision hdomination hcorrect hsimulation hmeas
  intro w
  rw [FiniteProb.prob_congr _ (fun ω => hrep ω w)]
  exact graph_occupancy G hreg ht R (U w) (hlocal w) (hhom w) e₀ (hzero w) hD hk hlower hupper

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/GraphNeighborhoodIso.lean ===== -/

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


/- ===== Source: MISLocal/GraphViewTransport.lean ===== -/

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


/- ===== Source: MISLocal/AnonymousRule.lean ===== -/

/-! An anonymous rule is one function on rooted, matrix-labeled views
modulo renaming vertices and edges. Vertex names are not algorithm inputs.
Private randomness uses the same finite alphabet and distribution at every
vertex; a sampled value can distinguish a root, but a skeleton name cannot. -/

open scoped Classical
namespace MISLocal
noncomputable section

abbrev EdgeMatrix (k : ℕ) := Fin k × Fin k → Bool

def transposeMatrix {k : ℕ} (M : EdgeMatrix k) : EdgeMatrix k := fun p => M p.swap

def matrixFlip (k : ℕ) (b : Bool) : EdgeMatrix k ≃ EdgeMatrix k where
  toFun M := if b then transposeMatrix M else M
  invFun M := if b then transposeMatrix M else M
  left_inv M := by cases b <;> rfl
  right_inv M := by cases b <;> rfl

structure NamedLocalView (V E : Type*) (k : ℕ) (Q : Type*) where
  root : V
  coin : Q
  edges : E → Option (V × V × EdgeMatrix k)

def renameEdgeDatum {V : Type*} {k : ℕ} (φ : V ≃ V) (b : Bool)
    (z : V × V × EdgeMatrix k) : V × V × EdgeMatrix k :=
  if b then (φ z.2.1,φ z.1,transposeMatrix z.2.2) else (φ z.1,φ z.2.1,z.2.2)

/-- Renaming changes only vertex/edge names and the arbitrary orientation
used to store an undirected edge matrix. It preserves all observed values. -/
def LocalViewRenaming {V E : Type*} {k : ℕ} {Q : Type*}
    (x y : NamedLocalView V E k Q) : Prop :=
  ∃ (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool),
    y.root = φ x.root ∧ y.coin = x.coin ∧
    ∀ i, y.edges (ψ i) = (x.edges i).map (renameEdgeDatum φ (flip i))

/-- `Quot` identifies every renaming above (and its equivalence closure).
There is no equivariance or probabilistic hypothesis in this definition. -/
abbrev AnonymousLocalView (V E : Type*) (k : ℕ) (Q : Type*) :=
  Quot (@LocalViewRenaming V E k Q)

abbrev AnonymousRule (V E : Type*) (k : ℕ) (Q : Type*) :=
  AnonymousLocalView V E k Q → Option (Fin k)

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {Q : Type}

def namedLocalView (r : ℕ) (v : V) (ω : ∀ i, matrixPrivateType G k (fun _ => Q) i) :
    NamedLocalView V G.edgeSet k Q where
  root := v
  coin := ω (Sum.inr v)
  edges i := if i ∈ seen G r v then some (edgeLeft G i,edgeRight G i,ω (Sum.inl i)) else none

def runAnonymous (A : AnonymousRule V G.edgeSet k Q) (r : ℕ)
    (v : V) (ω : ∀ i, matrixPrivateType G k (fun _ => Q) i) : Option (Fin k) :=
  A (Quot.mk _ (namedLocalView G r v ω))

theorem runAnonymous_local (A : AnonymousRule V G.edgeSet k Q) (r : ℕ) (v : V) :
    ReadsOnly (runAnonymous G A r v) (privateReads (seen G r) v) := by
  intro x y h
  have hc : x (Sum.inr v) = y (Sum.inr v) := h _ (by simp [privateReads])
  have he : (namedLocalView G r v x).edges = (namedLocalView G r v y).edges := by
    funext i
    by_cases hi : i ∈ seen G r v
    · have hxy := h (Sum.inl i) (by simp [privateReads, rawView, hi])
      simp only [namedLocalView, hi, if_true, hxy]
    · simp only [namedLocalView, hi, if_false]
  have hv : namedLocalView G r v x = namedLocalView G r v y := by
    exact congrArg₂ (fun coin edges => (⟨v,coin,edges⟩ : NamedLocalView V G.edgeSet k Q)) hc he
  exact congrArg (fun z => A (Quot.mk _ z)) hv

/-- Even on a graph with no automorphism sending `v` to `w`, a zero-round
anonymous rule cannot tell their skeleton names apart. Equal sampled private
values give equal outputs. -/
theorem runAnonymous_zero_same_coin (A : AnonymousRule V G.edgeSet k Q) (v w : V)
    (x y : ∀ i, matrixPrivateType G k (fun _ => Q) i)
    (hc : x (Sum.inr v) = y (Sum.inr w)) :
    runAnonymous G A 0 v x = runAnonymous G A 0 w y := by
  apply congrArg A
  apply Quot.sound
  refine ⟨Equiv.swap v w,Equiv.refl _,fun _ => false,?_,hc.symm,?_⟩
  · simp [namedLocalView]
  · intro i; simp [namedLocalView, seen]

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/AnonymousTransport.lean ===== -/

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


/- ===== Source: MISLocal/AnonymousOccupancy.lean ===== -/

/-! The occupancy bound with ordinary anonymity built into the algorithm
interface. There is no separately supplied locality or symmetry certificate. -/

open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every anonymous `(n+1)`-round rule on a finite regular graph with tree
edge neighborhoods and independent fair matrices satisfies the occupancy
bound. Private values are iid with any common finite distribution `R`. -/
theorem anonymous_graph_occupancy {d n k : ℕ}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    {Q : Type} [Fintype Q] (R : FiniteProb Q)
    (A : AnonymousRule V G.edgeSet k Q) (e₀ : G.edgeSet)
    (hzero : (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),runAnonymous G A (n+1) (edgeLeft G e₀) ω,
          runAnonymous G A (n+1) (edgeRight G e₀) ω)) = 0)
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob
      (fun ω => runAnonymous G A (n+1) (edgeLeft G e₀) ω ≠ none) ≤
        occupancyCap (n+1) ((d+1:ℕ):ℝ) :=
  graph_occupancy G hreg ht (fun _ => R) (runAnonymous G A (n+1))
    (runAnonymous_local G A (n+1)) (anonymous_homogeneous G hreg ht R A)
    e₀ hzero hD hk hlower hupper

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/AnonymousTapeReduction.lean ===== -/

/-! The fixed-tape averaging and finite obstruction with anonymous rules.
Their interfaces no longer require a view-symmetry or locality premise.
The concrete LOCAL simulation and its error estimates remain separate work. -/

open MeasureTheory
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V W : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [MeasurableSpace W]
    {d n k : ℕ} {Q : Type} [Fintype Q]

theorem averaged_anonymous_graph_occupancy
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    (R : FiniteProb Q) (ν : Measure W) [IsProbabilityMeasure ν]
    (A : W → AnonymousRule V G.edgeSet k Q) (e₀ : G.edgeSet)
    (hzero : ∀ w, (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω,
          runAnonymous G (A w) (n+1) (edgeRight G e₀) ω)) = 0)
    (hmeas : ∀ ω, MeasurableSet {w | runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω ≠ none})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).expect
      (fun ω => ν.real {w | runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω ≠ none}) ≤
        occupancyCap (n+1) ((d+1:ℕ):ℝ) :=
  average_fixed_tape_bound _ ν _ hmeas _ (fun w =>
    anonymous_graph_occupancy G hreg ht R (A w) e₀ (hzero w) hD hk hlower hupper)

theorem anonymous_graph_finite_obstruction {X : Type*}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    (R : FiniteProb Q) (ν : Measure W) [IsProbabilityMeasure ν]
    (H : (∀ i, matrixPrivateType G k (fun _ => Q) i) → SimpleGraph X) (C : Set X)
    (output candidates : (∀ i, matrixPrivateType G k (fun _ => Q) i) → W → Set X)
    (uniqueIDs : (∀ i, matrixPrivateType G k (fun _ => Q) i) → Prop)
    (A : W → AnonymousRule V G.edgeSet k Q) (e₀ : G.edgeSet)
    (hzero : ∀ w, (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω,
          runAnonymous G (A w) (n+1) (edgeRight G e₀) ω)) = 0)
    (hrep : ∀ ω w, Occupies C (repair (H ω) (candidates ω w)) ↔
      runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω ≠ none)
    (ε δ γ : ℝ) (hε : ε ≤ 1)
    (hcollision : (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob
      (fun ω => ¬uniqueIDs ω) ≤ δ)
    (hdomination : (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob
      (fun ω => ExternallyDominatable (H ω) C) ≤ γ)
    (hcorrect : ∀ ω, 1-ε ≤ ν.real {w | Maximal (H ω).IsIndepSet (output ω w)})
    (hsimulation : ∀ ω, uniqueIDs ω → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (H ω).Adj v x → (x ∈ candidates ω w ↔ x ∈ output ω w))
    (hmeas : ∀ ω, MeasurableSet {w | Occupies C (repair (H ω) (candidates ω w))})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (1-ε)*(1-δ-γ) ≤ occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  apply finite_obstruction (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))) ν H C
    output candidates uniqueIDs ε δ γ _ hε hcollision hdomination hcorrect hsimulation hmeas
  intro w
  rw [FiniteProb.prob_congr _ (fun ω => hrep ω w)]
  exact anonymous_graph_occupancy G hreg ht R (A w) e₀ (hzero w) hD hk hlower hupper

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/CliqueBlowup.lean ===== -/

/-! The actual graph given to a LOCAL algorithm: a clique at each skeleton
vertex, with the cross-clique adjacencies read from its incident matrices.
The stored orientation of a skeleton edge has no graph-theoretic meaning. -/

open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type*} (G : SimpleGraph V) {k : ℕ}

def crossCliqueAdj (M : G.edgeSet → EdgeMatrix k)
    (x y : V × Fin k) : Prop :=
  ∃ e, (edgeLeft G e = x.1 ∧ edgeRight G e = y.1 ∧ M e (x.2,y.2) = true) ∨
    (edgeRight G e = x.1 ∧ edgeLeft G e = y.1 ∧ M e (y.2,x.2) = true)

theorem crossCliqueAdj_symm (M : G.edgeSet → EdgeMatrix k)
    {x y : V × Fin k} (h : crossCliqueAdj G M x y) : crossCliqueAdj G M y x := by
  rcases h with ⟨e,h | h⟩
  · exact ⟨e,Or.inr ⟨h.2.1,h.1,h.2.2⟩⟩
  · exact ⟨e,Or.inl ⟨h.2.1,h.1,h.2.2⟩⟩

theorem crossCliqueAdj_skeleton (M : G.edgeSet → EdgeMatrix k)
    {x y : V × Fin k} (h : crossCliqueAdj G M x y) : G.Adj x.1 y.1 := by
  rcases h with ⟨e,h | h⟩
  · rw [← h.1,← h.2.1]; exact endpoint_adj G e
  · rw [← h.1,← h.2.1]; exact (endpoint_adj G e).symm

def cliqueBlowup (M : G.edgeSet → EdgeMatrix k) : SimpleGraph (V × Fin k) where
  Adj x y := (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ crossCliqueAdj G M x y
  symm := by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm,Ne.symm h.2⟩
    · exact Or.inr (crossCliqueAdj_symm G M h)
  loopless := by
    intro x h
    rcases h with h | h
    · exact h.2 rfl
    · exact G.irrefl (crossCliqueAdj_skeleton G M h)

def vertexClique (v : V) : Set (V × Fin k) := {x | x.1 = v}

theorem vertexClique_isClique (M : G.edgeSet → EdgeMatrix k) (v : V) :
    (cliqueBlowup G M).IsClique (vertexClique v) := by
  intro x hx y hy hxy
  apply Or.inl
  refine ⟨hx.trans hy.symm,?_⟩
  intro h
  exact hxy (Prod.ext (hx.trans hy.symm) h)

theorem blowup_adj_skeleton (M : G.edgeSet → EdgeMatrix k)
    {x y : V × Fin k} (h : (cliqueBlowup G M).Adj x y) :
    x.1 = y.1 ∨ G.Adj x.1 y.1 :=
  h.elim (fun h => Or.inl h.1) (fun h => Or.inr (crossCliqueAdj_skeleton G M h))

theorem blowup_ball_skeleton (M : G.edgeSet → EdgeMatrix k) (t : ℕ)
    (x y : V × Fin k) (h : InBall (cliqueBlowup G M) t x y) :
    InBall G t x.1 y.1 := by
  induction t generalizing x y with
  | zero => exact congrArg Prod.fst h
  | succ t ih =>
    rcases h with h | ⟨z,hxz,hzy⟩
    · exact Or.inl (congrArg Prod.fst h)
    · have hz := ih z y hzy
      rcases blowup_adj_skeleton G M hxz with h | h
      · rw [← h] at hz
        exact inBall_mono_succ G t x.1 y.1 hz
      · exact Or.inr ⟨z.1,h,hz⟩

theorem selected_matrix_edge (M : G.edgeSet → EdgeMatrix k) (e : G.edgeSet)
    (a b : Fin k) (h : M e (a,b) = true) :
    (cliqueBlowup G M).Adj (edgeLeft G e,a) (edgeRight G e,b) :=
  Or.inr ⟨e,Or.inl ⟨rfl,rfl,h⟩⟩

theorem repaired_clique_unique (M : G.edgeSet → EdgeMatrix k) (S : Set (V × Fin k))
    (v : V) {a b : Fin k}
    (ha : (v,a) ∈ repair (cliqueBlowup G M) S)
    (hb : (v,b) ∈ repair (cliqueBlowup G M) S) : a = b := by
  have h := clique_independent_at_most_one (cliqueBlowup G M)
    (vertexClique_isClique G M v) (repair_independent _ S)
    (show (v,a) ∈ vertexClique v from rfl) ha
    (show (v,b) ∈ vertexClique v from rfl) hb
  exact congrArg Prod.snd h

def repairedLabel (M : G.edgeSet → EdgeMatrix k) (S : Set (V × Fin k)) (v : V) :
    Option (Fin k) :=
  if h : ∃ a, (v,a) ∈ repair (cliqueBlowup G M) S then some h.choose else none

theorem repairedLabel_some (M : G.edgeSet → EdgeMatrix k) (S : Set (V × Fin k))
    (v : V) (a : Fin k) :
    repairedLabel G M S v = some a ↔ (v,a) ∈ repair (cliqueBlowup G M) S := by
  unfold repairedLabel
  split_ifs with h
  · constructor
    · intro he; exact (Option.some.inj he) ▸ h.choose_spec
    · intro ha
      exact congrArg some (repaired_clique_unique G M S v h.choose_spec ha)
  · simp only [reduceCtorEq, false_iff]
    exact fun ha => h ⟨a,ha⟩

theorem repairedLabel_occupies (M : G.edgeSet → EdgeMatrix k) (S : Set (V × Fin k))
    (v : V) : repairedLabel G M S v ≠ none ↔
      Occupies (vertexClique v) (repair (cliqueBlowup G M) S) := by
  unfold repairedLabel
  split_ifs with h
  · simp only [ne_eq, Option.some_ne_none, not_false_eq_true, true_iff]
    exact ⟨(v,h.choose),rfl,h.choose_spec⟩
  · simp only [ne_eq, not_true_eq_false, false_iff]
    rintro ⟨⟨w,a⟩,hw,ha⟩
    exact h ⟨a,hw ▸ ha⟩

theorem repairedLabel_noConflict (M : G.edgeSet → EdgeMatrix k)
    (S : Set (V × Fin k)) (e : G.edgeSet) :
    ¬selectedConflict (fun M a b => M (a,b)=true)
      (M e,repairedLabel G M S (edgeLeft G e),repairedLabel G M S (edgeRight G e)) := by
  unfold selectedConflict
  generalize hl : repairedLabel G M S (edgeLeft G e) = l
  generalize hr : repairedLabel G M S (edgeRight G e) = r
  cases l with
  | none => simp
  | some a =>
    cases r with
    | none => simp
    | some b =>
      intro hab
      have ha := (repairedLabel_some G M S (edgeLeft G e) a).mp hl
      have hb := (repairedLabel_some G M S (edgeRight G e) b).mp hr
      exact ha.2 _ (selected_matrix_edge G M e a b hab) hb.1

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/UniformLocalProtocol.lean ===== -/

/-! A uniform synchronous LOCAL program. The functions receive identifiers,
private tapes, and the identifiers/states at incident ports. They never receive
an underlying vertex name or the entire graph. Giving neighbor identifiers at
time zero only strengthens the model. On a legal ID assignment the neighbors
are distinct, so sorting these IDs supplies a legal port numbering.

States and messages have no size restriction. Sending each whole state is a
full-information simulation of arbitrary port-dependent messages. -/

open scoped Classical
namespace MISLocal
noncomputable section

structure UniformLocalProtocol (n : ℕ) (Tape State : Type*) where
  init : Fin n → Finset (Fin n) → Tape → State
  step : ℕ → Fin n → Tape → State → Finset (Fin n × State) → State
  output : Fin n → State → Bool

namespace UniformLocalProtocol

variable {n : ℕ} {Tape State V : Type*} [Fintype V]
    (A : UniformLocalProtocol n Tape State)

def neighbors (G : SimpleGraph V) (ids : V → Fin n) (v : V) : Finset (Fin n) :=
  (Finset.univ.filter (G.Adj v)).image ids

def run (G : SimpleGraph V) (ids : V → Fin n) (W : Fin n → Tape) : ℕ → V → State
  | 0,v => A.init (ids v) (neighbors G ids v) (W (ids v))
  | t+1,v => A.step t (ids v) (W (ids v)) (run G ids W t v)
      ((Finset.univ.filter (G.Adj v)).image (fun u => (ids u,run G ids W t u)))

def candidates (G : SimpleGraph V) (ids : V → Fin n) (W : Fin n → Tape)
    (t : ℕ) : Set V := {v | A.output (ids v) (A.run G ids W t v) = true}

omit A in
theorem neighbors_eq_of_ids {G : SimpleGraph V} {x y : V → Fin n} {v : V}
    (h : ∀ u, G.Adj v u → x u = y u) : neighbors G x v = neighbors G y v := by
  apply Finset.image_congr
  intro u hu
  exact h u (Finset.mem_filter.mp hu).2

/-- Initialization can read neighbors' IDs. Accordingly a T-round execution
reads only identifiers in the radius-(T+1) ball, including its own tape. -/
theorem run_local (G : SimpleGraph V) (t : ℕ) (v : V)
    (x y : V → Fin n) (W : Fin n → Tape)
    (h : ∀ u, InBall G (t+1) v u → x u = y u) :
    A.run G x W t v = A.run G y W t v := by
  induction t generalizing v with
  | zero =>
    have hv := h v (inBall_self G 1 v)
    have hn : neighbors G x v = neighbors G y v :=
      neighbors_eq_of_ids (fun u hu => h u (Or.inr ⟨u,hu,rfl⟩))
    simp only [run,hv,hn]
  | succ t ih =>
    have hv := h v (inBall_self G (t+1+1) v)
    have hs := ih v (fun u hu => h u (inBall_mono_succ G (t+1) v u hu))
    have hm :
        (Finset.univ.filter (G.Adj v)).image (fun u => (x u,A.run G x W t u)) =
        (Finset.univ.filter (G.Adj v)).image (fun u => (y u,A.run G y W t u)) := by
      apply Finset.image_congr
      intro u hu
      have hvu := (Finset.mem_filter.mp hu).2
      have hid := h u (Or.inr ⟨u,hvu,inBall_self G (t+1) u⟩)
      exact Prod.ext hid (ih u (fun w hw => h w (Or.inr ⟨u,hvu,hw⟩)))
    simp only [run,hv,hs,hm]

theorem candidates_local (G : SimpleGraph V) (t : ℕ) (v : V)
    (x y : V → Fin n) (W : Fin n → Tape)
    (h : ∀ u, InBall G (t+1) v u → x u = y u) :
    v ∈ A.candidates G x W t ↔ v ∈ A.candidates G y W t := by
  have hv := h v (inBall_self G (t+1) v)
  simp only [candidates,Set.mem_setOf_eq,hv,A.run_local G t v x y W h]

/-- The completion may depend on the graph and IDs, but not the tape table. -/
theorem completed_ID_simulation (G : SimpleGraph (Fin n)) (t : ℕ) (v : Fin n)
    (ids : Fin n → Fin n) (W : Fin n → Tape)
    (hinj : Set.InjOn ids {u | InBall G (t+1) v u}) :
    A.run G (completeIDs {u | InBall G (t+1) v u} ids) W t v =
      A.run G ids W t v := by
  apply A.run_local
  intro u hu
  exact completeIDs_agrees _ ids hinj u hu

omit A in
theorem neighborImage_transport {U B : Type*} [Fintype U] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph U) (φ : V ≃ U)
    (v : V) (f : V → B) (g : U → B)
    (hrow : ∀ u, G.Adj v u ↔ H.Adj (φ v) (φ u))
    (hdata : ∀ u, G.Adj v u → f u = g (φ u)) :
    (Finset.univ.filter (G.Adj v)).image f =
      (Finset.univ.filter (H.Adj (φ v))).image g := by
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,huz⟩ := Finset.mem_image.mp hz
    have ha := (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨φ u,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(hrow u).mp ha⟩,(hdata u ha).symm.trans huz⟩
  · intro hz
    obtain ⟨u,hu,huz⟩ := Finset.mem_image.mp hz
    have ha : G.Adj v (φ.symm u) :=
      (hrow (φ.symm u)).mpr (by simpa using (Finset.mem_filter.mp hu).2)
    have hd := hdata (φ.symm u) ha
    rw [φ.apply_symm_apply] at hd
    exact Finset.mem_image.mpr ⟨φ.symm u,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,ha⟩,hd.trans huz⟩

/-- Local graph matching is sufficient; a global graph automorphism is not
needed. Only rows at distance at most T and IDs at distance at most T+1
enter the execution. Both graph and tape data are included. -/
theorem run_transport {U : Type*} [Fintype U] (G : SimpleGraph V) (H : SimpleGraph U) (φ : V ≃ U)
    (ids : V → Fin n) (ids' : U → Fin n) (W : Fin n → Tape) (t : ℕ) (v : V)
    (hids : ∀ u, InBall G (t+1) v u → ids u = ids' (φ u))
    (hrows : ∀ u, InBall G t v u → ∀ w,
      G.Adj u w ↔ H.Adj (φ u) (φ w)) :
    A.run G ids W t v = A.run H ids' W t (φ v) := by
  induction t generalizing v with
  | zero =>
    have hv := hids v (inBall_self G 1 v)
    have hr := hrows v rfl
    have hn : neighbors G ids v = neighbors H ids' (φ v) :=
      neighborImage_transport G H φ v ids ids' hr
        (fun u hu => hids u (Or.inr ⟨u,hu,rfl⟩))
    simp only [run,hv,hn]
  | succ t ih =>
    have hv := hids v (inBall_self G (t+1+1) v)
    have hr := hrows v (inBall_self G (t+1) v)
    have hs := ih v
      (fun u hu => hids u (inBall_mono_succ G (t+1) v u hu))
      (fun u hu => hrows u (inBall_mono_succ G t v u hu))
    have hn :
        (Finset.univ.filter (G.Adj v)).image (fun u => (ids u,A.run G ids W t u)) =
        (Finset.univ.filter (H.Adj (φ v))).image
          (fun u => (ids' u,A.run H ids' W t u)) := by
      apply neighborImage_transport G H φ v _ _ hr
      intro u hu
      refine Prod.ext (hids u (Or.inr ⟨u,hu,inBall_self G (t+1) u⟩)) ?_
      exact ih u (fun w hw => hids w (Or.inr ⟨u,hu,hw⟩))
        (fun w hw => hrows w (Or.inr ⟨u,hu,hw⟩))
    simp only [run,hv,hs,hn]

theorem candidates_transport {U : Type*} [Fintype U] (G : SimpleGraph V) (H : SimpleGraph U) (φ : V ≃ U)
    (ids : V → Fin n) (ids' : U → Fin n) (W : Fin n → Tape) (t : ℕ) (v : V)
    (hids : ∀ u, InBall G (t+1) v u → ids u = ids' (φ u))
    (hrows : ∀ u, InBall G t v u → ∀ w,
      G.Adj u w ↔ H.Adj (φ u) (φ w)) :
    v ∈ A.candidates G ids W t ↔ φ v ∈ A.candidates H ids' W t := by
  have hv := hids v (inBall_self G (t+1) v)
  simp only [candidates,Set.mem_setOf_eq,hv,A.run_transport G H φ ids ids' W t v hids hrows]

end UniformLocalProtocol
end
end MISLocal


/- ===== Source: MISLocal/UniformExtraction.lean ===== -/

/-! Exact uniformity, including the whole extracted vector. A surjective
additive map between finite groups sends uniform input to uniform output.
No pairwise-independence shortcut is used in this step. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section
namespace FiniteProb

theorem uniform_map_equiv {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    [Nonempty B] (e : A ≃ B) : (uniform A).map e = uniform B := by
  ext b
  rw [map_equiv_weight]
  simp only [uniform,Fintype.card_congr e]

theorem pi_uniform {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    pi (fun i => uniform (A i)) = uniform (∀ i, A i) := by
  ext x
  simp only [pi,uniform,Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

def additiveFiberSplit {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Surjective f) :
    A ≃ B × {a : A // f a = 0} where
  toFun a := (f a,⟨a-(hf (f a)).choose,by simp [(hf (f a)).choose_spec]⟩)
  invFun z := (hf z.1).choose + z.2.val
  left_inv a := by simp
  right_inv z := by
    apply Prod.ext
    · simp [(hf z.1).choose_spec,z.2.property]
    · apply Subtype.ext
      simp [(hf z.1).choose_spec,z.2.property]

theorem uniform_map_surjective_addHom {A B : Type*}
    [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Surjective f) :
    (uniform A).map f = uniform B := by
  ext b
  letI : Nonempty {a : A // f a = 0} := ⟨⟨0,map_zero f⟩⟩
  change (uniform A).prob (fun a => f a = b) = _
  simpa only [additiveFiberSplit,uniform,one_div] using
    uniform_first_coordinate (additiveFiberSplit f hf) b

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/DirectedIdentifiers.lean ===== -/

/-! An actual extractor on the fair edge matrices. The two orientations use
disjoint off-diagonal blocks. All outgoing blocks at a vertex are added, so
the extractor does not choose or order an incident edge. A chosen incident
edge occurs only in the surjectivity proof. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

def lowerHalf (m : ℕ) (i : Fin m) : Fin (2*m) := ⟨i.val,by omega⟩
def upperHalf (m : ℕ) (i : Fin m) : Fin (2*m) := ⟨m+i.val,by omega⟩

def directedBlockPosition (m : ℕ) (z : Bool × (Fin m × Fin m)) :
    Fin (2*m) × Fin (2*m) :=
  if z.1 then (upperHalf m z.2.2,lowerHalf m z.2.1)
    else (lowerHalf m z.2.1,upperHalf m z.2.2)

theorem directedBlockPosition_injective (m : ℕ) :
    Function.Injective (directedBlockPosition m) := by
  rintro ⟨b,p⟩ ⟨c,q⟩ h
  cases b <;> cases c
  · have h₁ := congrArg (fun x => x.1.val) h
    have h₂ := congrArg (fun x => x.2.val) h
    simp only [directedBlockPosition,Bool.false_eq_true,if_false,lowerHalf,upperHalf,Prod.fst,Prod.snd] at h₁ h₂
    exact Prod.ext rfl (Prod.ext (Fin.ext h₁) (Fin.ext (Nat.add_left_cancel h₂)))
  · have h₁ := congrArg (fun x => x.1.val) h
    simp only [directedBlockPosition,Bool.false_eq_true,if_false,if_true,lowerHalf,upperHalf,Prod.fst,Prod.snd] at h₁
    have hp := p.1.isLt
    omega
  · have h₁ := congrArg (fun x => x.1.val) h
    simp only [directedBlockPosition,Bool.false_eq_true,if_false,if_true,lowerHalf,upperHalf,Prod.fst,Prod.snd] at h₁
    have hq := q.1.isLt
    omega
  · have h₁ := congrArg (fun x => x.1.val) h
    have h₂ := congrArg (fun x => x.2.val) h
    simp only [directedBlockPosition,if_true,lowerHalf,upperHalf,Prod.fst,Prod.snd] at h₁ h₂
    exact Prod.ext rfl (Prod.ext (Fin.ext h₂) (Fin.ext (Nat.add_left_cancel h₁)))

def blockRestriction {E : Type*} (m : ℕ) :
    (E → Fin (2*m) × Fin (2*m) → ZMod 2) →+
      ((E × Bool) → Fin m × Fin m → ZMod 2) where
  toFun x eb p := x eb.1 (directedBlockPosition m (eb.2,p))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem blockRestriction_surjective {E : Type*} (m : ℕ) :
    Function.Surjective (blockRestriction (E := E) m) := by
  intro y
  refine ⟨fun e => Function.extend (directedBlockPosition m)
    (fun bp => y (e,bp.1) bp.2) (fun _ => 0),?_⟩
  funext eb p
  change Function.extend (directedBlockPosition m)
    (fun bp => y (eb.1,bp.1) bp.2) (fun _ => 0)
      (directedBlockPosition m (eb.2,p)) = _
  exact (directedBlockPosition_injective m).extend_apply _ _ (eb.2,p)

/-- Add all source strings having the indicated endpoint. -/
def endpointSum {J V A : Type*} [Fintype J] [AddCommGroup A]
    (endpoint : J → V) : (J → A) →+ (V → A) where
  toFun x v := ∑ j, if endpoint j = v then x j else 0
  map_zero' := by ext v; simp
  map_add' := by
    intro x y; ext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : endpoint j = v <;> simp [h]

theorem endpointSum_surjective {J V A : Type*} [Fintype J] [AddCommGroup A]
    (endpoint : J → V) (h : Function.Surjective endpoint) :
    Function.Surjective (endpointSum (A := A) endpoint) := by
  let chooseSource : V → J := fun v => (h v).choose
  have hs (v : V) : endpoint (chooseSource v) = v := (h v).choose_spec
  intro y
  refine ⟨fun j => if j = chooseSource (endpoint j) then y (endpoint j) else 0,?_⟩
  funext v
  change (∑ j, if endpoint j = v then
    (if j = chooseSource (endpoint j) then y (endpoint j) else 0) else 0) = y v
  rw [Finset.sum_eq_single (chooseSource v)]
  · simp [hs]
  · intro j _ hj
    by_cases he : endpoint j = v
    · simp [he,hj]
    · simp [he]
  · simp

def bitGroupEquiv : Bool ≃ ZMod 2 :=
  Fintype.equivOfCardEq (by simp [ZMod.card])

def matrixBitGroupEquiv {E : Type*} (m : ℕ) :
    (E → EdgeMatrix (2*m)) ≃ (E → Fin (2*m) × Fin (2*m) → ZMod 2) where
  toFun x e p := bitGroupEquiv (x e p)
  invFun x e p := bitGroupEquiv.symm (x e p)
  left_inv x := by ext e p; exact bitGroupEquiv.symm_apply_apply _
  right_inv x := by ext e p; exact bitGroupEquiv.apply_symm_apply _

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

def outgoingEndpoint (eb : G.edgeSet × Bool) : V :=
  if eb.2 then edgeRight G eb.1 else edgeLeft G eb.1

theorem outgoingEndpoint_surjective (hdegree : ∀ v, 0 < G.degree v) :
    Function.Surjective (outgoingEndpoint G) := by
  intro v
  have hc : 0 < (Finset.univ.filter
      (edgeIncident (edgeLeft G) (edgeRight G) v)).card := by
    rw [incident_card_eq_degree G v]; exact hdegree v
  obtain ⟨e,he⟩ := Finset.card_pos.mp hc
  rcases (Finset.mem_filter.mp he).2 with hl | hr
  · exact ⟨(e,false),hl⟩
  · exact ⟨(e,true),hr⟩

def vertexBlockSum (m : ℕ) :
    (G.edgeSet → Fin (2*m) × Fin (2*m) → ZMod 2) →+
      (V → Fin m × Fin m → ZMod 2) :=
  (endpointSum (A := Fin m × Fin m → ZMod 2) (outgoingEndpoint G)).comp
    (blockRestriction m)

def extractedBlockStrings (m : ℕ) (M : G.edgeSet → EdgeMatrix (2*m)) :
    V → Fin m × Fin m → ZMod 2 :=
  vertexBlockSum G m (matrixBitGroupEquiv m M)

theorem extractedBlockStrings_jointly_uniform (m : ℕ)
    (hdegree : ∀ v, 0 < G.degree v) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))).map
      (extractedBlockStrings G m) = FiniteProb.uniform (V → Fin m × Fin m → ZMod 2) := by
  have hb : FiniteProb.fairBits (Fin (2*m) × Fin (2*m)) =
      FiniteProb.uniform (EdgeMatrix (2*m)) := FiniteProb.pi_uniform
  rw [hb,FiniteProb.pi_uniform]
  change (FiniteProb.uniform (G.edgeSet → EdgeMatrix (2*m))).map
    (fun M => vertexBlockSum G m (matrixBitGroupEquiv m M)) = _
  rw [← FiniteProb.map_comp,FiniteProb.uniform_map_equiv]
  apply FiniteProb.uniform_map_surjective_addHom
  exact (endpointSum_surjective (outgoingEndpoint G) (outgoingEndpoint_surjective G hdegree)).comp
    (blockRestriction_surjective m)

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/IdentifierBits.lean ===== -/

/-! Convert disjoint pieces of each uniform vertex string into legal-range
tentative IDs. On the power-of-two size sequence no modulo bias is needed. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

def wordIdentifierEquiv (b : ℕ) : (Fin b → ZMod 2) ≃ Fin (2^b) :=
  Fintype.equivOfCardEq (by simp [ZMod.card])

def readIdentifierBits {V : Type*} {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m)) :
    (V → Fin m × Fin m → ZMod 2) →+ ((V × Fin (2*m)) → Fin b → ZMod 2) where
  toFun x va t := x va.1 (pack (va.2,t))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem readIdentifierBits_surjective {V : Type*} {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m)) :
    Function.Surjective (readIdentifierBits (V := V) pack) := by
  intro y
  refine ⟨fun v => Function.extend pack (fun pair => y (v,pair.1) pair.2) (fun _ => 0),?_⟩
  funext va t
  change Function.extend pack (fun pair => y (va.1,pair.1) pair.2) (fun _ => 0) (pack (va.2,t)) = _
  exact pack.injective.extend_apply _ _ _

def wordsIdentifierEquiv {X : Type*} (b : ℕ) :
    (X → Fin b → ZMod 2) ≃ (X → Fin (2^b)) :=
  Equiv.piCongrRight (fun _ => wordIdentifierEquiv b)

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m b : ℕ} (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))

def extractedIdentifiers (M : G.edgeSet → EdgeMatrix (2*m)) :
    (V × Fin (2*m)) → Fin (2^b) :=
  wordsIdentifierEquiv b (readIdentifierBits pack (extractedBlockStrings G m M))

theorem extractedIdentifiers_jointly_uniform (hdegree : ∀ v, 0 < G.degree v) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))).map
      (extractedIdentifiers G pack) = FiniteProb.uniform ((V × Fin (2*m)) → Fin (2^b)) := by
  let μ := FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))
  calc
    μ.map (extractedIdentifiers G pack) =
        ((μ.map (extractedBlockStrings G m)).map (readIdentifierBits pack)).map
          (wordsIdentifierEquiv b) := by rw [FiniteProb.map_comp,FiniteProb.map_comp]; rfl
    _ = _ := by
      rw [extractedBlockStrings_jointly_uniform G m hdegree,
        FiniteProb.uniform_map_surjective_addHom _ (readIdentifierBits_surjective pack),
        FiniteProb.uniform_map_equiv]

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/ViewSimulation.lean ===== -/

/-! A concrete LOCAL simulation on a named edge snapshot. Every definition
also makes sense on malformed snapshots, permitting an actual `Quot.lift`
to the anonymous input type. Equivariance is proved pointwise. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

abbrev EdgeDatum (V : Type*) (k : ℕ) := V × V × EdgeMatrix k

def datumSkeleton {V : Type*} {k : ℕ} (z : EdgeDatum V k) (v w : V) : Prop :=
  (z.1 = v ∧ z.2.1 = w) ∨ (z.2.1 = v ∧ z.1 = w)

def datumCross {V : Type*} {k : ℕ} (z : EdgeDatum V k)
    (x y : V × Fin k) : Prop :=
  (z.1 = x.1 ∧ z.2.1 = y.1 ∧ z.2.2 (x.2,y.2) = true) ∨
    (z.2.1 = x.1 ∧ z.1 = y.1 ∧ z.2.2 (y.2,x.2) = true)

theorem datumSkeleton_rename {V : Type*} {k : ℕ} (φ : V ≃ V) (b : Bool)
    (z : EdgeDatum V k) (v w : V) :
    datumSkeleton (renameEdgeDatum φ b z) (φ v) (φ w) ↔ datumSkeleton z v w := by
  cases b <;> simp [datumSkeleton,renameEdgeDatum,or_comm,and_comm]

theorem datumCross_rename {V : Type*} {k : ℕ} (φ : V ≃ V) (b : Bool)
    (z : EdgeDatum V k) (x y : V × Fin k) :
    datumCross (renameEdgeDatum φ b z) (φ x.1,x.2) (φ y.1,y.2) ↔ datumCross z x y := by
  cases b <;> simp [datumCross,renameEdgeDatum,transposeMatrix,or_comm]

def hasDatum {V E : Type*} {k : ℕ} {Q : Type*}
    (x : NamedLocalView V E k Q) (P : EdgeDatum V k → Prop) : Prop :=
  ∃ e, ∃ z, x.edges e = some z ∧ P z

theorem hasDatum_rename {V E : Type*} {k : ℕ} {Q : Type*}
    {x y : NamedLocalView V E k Q} (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e)))
    (P P' : EdgeDatum V k → Prop)
    (hP : ∀ e z, P' (renameEdgeDatum φ (flip e) z) ↔ P z) :
    hasDatum y P' ↔ hasDatum x P := by
  have he (e : E) : (∃ z, y.edges (ψ e) = some z ∧ P' z) ↔
      ∃ z, x.edges e = some z ∧ P z := by
    rw [h e]
    cases hx : x.edges e with
    | none => simp
    | some z => simpa using hP e z
  constructor
  · rintro ⟨e,hz⟩
    refine ⟨ψ.symm e,(he (ψ.symm e)).mp ?_⟩
    simpa only [ψ.apply_symm_apply] using hz
  · rintro ⟨e,hz⟩
    exact ⟨ψ e,(he e).mpr hz⟩

def snapshotSkeleton {V E : Type*} {k : ℕ} {Q : Type*}
    (x : NamedLocalView V E k Q) : SimpleGraph V where
  Adj v w := v ≠ w ∧ hasDatum x (fun z => datumSkeleton z v w)
  symm := by
    rintro v w ⟨hne,e,z,he,hz⟩
    refine ⟨hne.symm,e,z,he,?_⟩
    exact hz.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)
  loopless := fun _ h => h.1 rfl

def snapshotBlowup {V E : Type*} {k : ℕ} {Q : Type*}
    (x : NamedLocalView V E k Q) : SimpleGraph (V × Fin k) where
  Adj v w := (v.1 = w.1 ∧ v.2 ≠ w.2) ∨
    (v.1 ≠ w.1 ∧ hasDatum x (fun z => datumCross z v w))
  symm := by
    rintro v w (h | ⟨hne,e,z,he,hz⟩)
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · refine Or.inr ⟨hne.symm,e,z,he,?_⟩
      exact hz.elim (fun h => Or.inr ⟨h.2.1,h.1,h.2.2⟩)
        (fun h => Or.inl ⟨h.2.1,h.1,h.2.2⟩)
  loopless := by
    intro v h
    rcases h with h | h
    · exact h.2 rfl
    · exact h.1 rfl

def cliqueVertexRename {V : Type*} (k : ℕ) (φ : V ≃ V) :
    (V × Fin k) ≃ (V × Fin k) := Equiv.prodCongr φ (Equiv.refl _)

theorem snapshotSkeleton_rename {V E : Type*} {k : ℕ} {Q : Type*}
    {x y : NamedLocalView V E k Q} (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e))) (v w : V) :
    (snapshotSkeleton y).Adj (φ v) (φ w) ↔ (snapshotSkeleton x).Adj v w := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [φ.injective.ne_iff]
  exact and_congr_right (fun _ => hasDatum_rename φ ψ flip h _ _
    (fun e z => datumSkeleton_rename φ (flip e) z v w))

theorem snapshotBlowup_rename {V E : Type*} {k : ℕ} {Q : Type*}
    {x y : NamedLocalView V E k Q} (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e)))
    (v w : V × Fin k) :
    (snapshotBlowup y).Adj (cliqueVertexRename k φ v) (cliqueVertexRename k φ w) ↔
      (snapshotBlowup x).Adj v w := by
  change ((φ v.1 = φ w.1 ∧ v.2 ≠ w.2) ∨
    (φ v.1 ≠ φ w.1 ∧ hasDatum y (fun z => datumCross z (φ v.1,v.2) (φ w.1,w.2)))) ↔ _
  simp only [φ.injective.eq_iff,φ.injective.ne_iff]
  exact or_congr Iff.rfl (and_congr_right (fun _ => hasDatum_rename φ ψ flip h _ _
    (fun e z => datumCross_rename φ (flip e) z v w)))

def datumBlockString {V : Type*} (m : ℕ) (v : V) (z : EdgeDatum V (2*m)) :
    Fin m × Fin m → ZMod 2 := fun p =>
  (if z.1 = v then bitGroupEquiv (z.2.2 (directedBlockPosition m (false,p))) else 0) +
    (if z.2.1 = v then bitGroupEquiv (z.2.2 (directedBlockPosition m (true,p))) else 0)

theorem datumBlockString_rename {V : Type*} (m : ℕ) (φ : V ≃ V) (b : Bool)
    (v : V) (z : EdgeDatum V (2*m)) :
    datumBlockString m (φ v) (renameEdgeDatum φ b z) = datumBlockString m v z := by
  funext p
  cases b <;> simp [datumBlockString,renameEdgeDatum,transposeMatrix,
    directedBlockPosition,add_comm]

def snapshotBlockStrings {V E : Type*} [Fintype E] (m : ℕ) {Q : Type*}
    (x : NamedLocalView V E (2*m) Q) (v : V) : Fin m × Fin m → ZMod 2 :=
  ∑ e, (x.edges e).elim 0 (datumBlockString m v)

theorem snapshotBlockStrings_rename {V E : Type*} [Fintype E] (m : ℕ) {Q : Type*}
    {x y : NamedLocalView V E (2*m) Q} (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e))) (v : V) :
    snapshotBlockStrings m y (φ v) = snapshotBlockStrings m x v := by
  unfold snapshotBlockStrings
  rw [← ψ.sum_comp (fun e => (y.edges e).elim 0 (datumBlockString m (φ v)))]
  apply Finset.sum_congr rfl
  intro e _
  rw [h e]
  cases x.edges e with
  | none => rfl
  | some z => exact datumBlockString_rename m φ (flip e) v z

end
end MISLocal


/- ===== Source: MISLocal/AnonymousLocalReduction.lean ===== -/

/-! Construct the anonymous rule from a LOCAL program and a fixed ID-indexed
tape table. A neighborhood collision gate precedes the simulation, and
conflict deletion follows it. Anonymity is obtained by a proved quotient lift. -/

open scoped Classical
namespace MISLocal
noncomputable section

theorem inBall_equiv {V : Type*} (G H : SimpleGraph V) (φ : V ≃ V)
    (h : ∀ v w, H.Adj (φ v) (φ w) ↔ G.Adj v w) (t : ℕ) (v w : V) :
    InBall H t (φ v) (φ w) ↔ InBall G t v w := by
  induction t generalizing v w with
  | zero => exact φ.injective.eq_iff
  | succ t ih =>
    constructor
    · rintro (hw | ⟨z,hvz,hzw⟩)
      · exact Or.inl (φ.injective hw)
      · have hz : H.Adj (φ v) (φ (φ.symm z)) := by simpa using hvz
        have hb : InBall H t (φ (φ.symm z)) (φ w) := by simpa using hzw
        exact Or.inr ⟨φ.symm z,(h v _).mp hz,(ih _ _).mp hb⟩
    · rintro (hw | ⟨z,hvz,hzw⟩)
      · exact Or.inl (congrArg φ hw)
      · exact Or.inr ⟨φ z,(h v z).mpr hvz,(ih z w).mpr hzw⟩

theorem repair_equiv {V : Type*} (G H : SimpleGraph V) (φ : V ≃ V)
    (S S' : Set V) (hG : ∀ v w, H.Adj (φ v) (φ w) ↔ G.Adj v w)
    (hS : ∀ v, φ v ∈ S' ↔ v ∈ S) (v : V) :
    φ v ∈ repair H S' ↔ v ∈ repair G S := by
  constructor
  · rintro ⟨hv,hn⟩
    exact ⟨(hS v).mp hv,fun w hw hsw => hn (φ w) ((hG v w).mpr hw) ((hS w).mpr hsw)⟩
  · rintro ⟨hv,hn⟩
    refine ⟨(hS v).mpr hv,fun w hw hsw => ?_⟩
    have ha : H.Adj (φ v) (φ (φ.symm w)) := by simpa using hw
    have hs : φ (φ.symm w) ∈ S' := by simpa using hsw
    exact hn (φ.symm w) ((hG v _).mp ha) ((hS _).mp hs)

def chooseLabel {k : ℕ} (P : Fin k → Prop) : Option (Fin k) :=
  if h : ∃ a, P a then some h.choose else none

theorem chooseLabel_congr {k : ℕ} {P Q : Fin k → Prop}
    (h : ∀ a, P a ↔ Q a) : chooseLabel P = chooseLabel Q := by
  have he : P = Q := funext (fun a => propext (h a))
  rw [he]

theorem chooseLabel_mem {k : ℕ} {P : Fin k → Prop} {a : Fin k}
    (h : chooseLabel P = some a) : P a := by
  unfold chooseLabel at h
  split_ifs at h with hp
  · exact (Option.some.inj h) ▸ hp.choose_spec

theorem chooseLabel_nonempty {k : ℕ} (P : Fin k → Prop) :
    chooseLabel P ≠ none ↔ ∃ a, P a := by
  unfold chooseLabel
  split_ifs <;> simp_all

variable {V E : Type*} [Fintype V] [Fintype E] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))

def snapshotIdentifiers (x : NamedLocalView V E (2*m) Unit) :
    (V × Fin (2*m)) → Fin (2^b) := fun va =>
  wordIdentifierEquiv b (fun t => snapshotBlockStrings m x va.1 (pack (va.2,t)))

omit [Fintype V] in
theorem snapshotIdentifiers_rename {x y : NamedLocalView V E (2*m) Unit}
    (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e)))
    (va : V × Fin (2*m)) :
    snapshotIdentifiers pack y (cliqueVertexRename (2*m) φ va) = snapshotIdentifiers pack x va := by
  change wordIdentifierEquiv b (fun t => snapshotBlockStrings m y (φ va.1) (pack (va.2,t))) = _
  rw [snapshotBlockStrings_rename m φ ψ flip h]
  rfl

def snapshotUnique (T : ℕ) (x : NamedLocalView V E (2*m) Unit) (v : V) : Prop :=
  Set.InjOn (snapshotIdentifiers pack x) {z | InBall (snapshotSkeleton x) (T+1) v z.1}

omit [Fintype V] in
theorem snapshotUnique_rename (T : ℕ) {x y : NamedLocalView V E (2*m) Unit}
    (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e))) (v : V) :
    snapshotUnique pack T y (φ v) ↔ snapshotUnique pack T x v := by
  let Φ := cliqueVertexRename (2*m) φ
  have hid := snapshotIdentifiers_rename pack φ ψ flip h
  have hb (z : V × Fin (2*m)) :
      InBall (snapshotSkeleton y) (T+1) (φ v) (Φ z).1 ↔
        InBall (snapshotSkeleton x) (T+1) v z.1 :=
    inBall_equiv _ _ φ (snapshotSkeleton_rename φ ψ flip h) (T+1) v z.1
  constructor
  · intro hu z hz w hw he
    have hids : snapshotIdentifiers pack y (Φ z) = snapshotIdentifiers pack y (Φ w) := by
      rw [hid z,hid w]; exact he
    exact Φ.injective (hu ((hb z).mpr hz) ((hb w).mpr hw) hids)
  · intro hu z hz w hw he
    have hzb := (hb (Φ.symm z)).mp (by simpa [Φ] using hz)
    have hwb := (hb (Φ.symm w)).mp (by simpa [Φ] using hw)
    have hids : snapshotIdentifiers pack x (Φ.symm z) = snapshotIdentifiers pack x (Φ.symm w) := by
      rw [← hid (Φ.symm z),← hid (Φ.symm w)]
      simpa [Φ] using he
    exact Φ.symm.injective (hu hzb hwb hids)

variable {Tape State : Type*} (A : UniformLocalProtocol (2^b) Tape State)
    (W : Fin (2^b) → Tape) (T : ℕ)

def snapshotCandidates (x : NamedLocalView V E (2*m) Unit) : Set (V × Fin (2*m)) :=
  {z | snapshotUnique pack T x z.1 ∧
    z ∈ A.candidates (snapshotBlowup x) (snapshotIdentifiers pack x) W T}

theorem snapshotCandidates_rename {x y : NamedLocalView V E (2*m) Unit}
    (φ : V ≃ V) (ψ : E ≃ E) (flip : E → Bool)
    (h : ∀ e, y.edges (ψ e) = (x.edges e).map (renameEdgeDatum φ (flip e)))
    (z : V × Fin (2*m)) :
    cliqueVertexRename (2*m) φ z ∈ snapshotCandidates pack A W T y ↔
      z ∈ snapshotCandidates pack A W T x := by
  apply and_congr (snapshotUnique_rename pack T φ ψ flip h z.1)
  apply Iff.symm
  apply A.candidates_transport _ _ (cliqueVertexRename (2*m) φ)
  · intro u _; exact (snapshotIdentifiers_rename pack φ ψ flip h u).symm
  · intro u _ w; exact (snapshotBlowup_rename φ ψ flip h u w).symm

def snapshotRepairedLabel (x : NamedLocalView V E (2*m) Unit) : Option (Fin (2*m)) :=
  chooseLabel (fun a => (x.root,a) ∈ repair (snapshotBlowup x) (snapshotCandidates pack A W T x))

theorem snapshotRepairedLabel_rename {x y : NamedLocalView V E (2*m) Unit}
    (h : LocalViewRenaming x y) :
    snapshotRepairedLabel pack A W T x = snapshotRepairedLabel pack A W T y := by
  obtain ⟨φ,ψ,flip,hr,_,he⟩ := h
  apply chooseLabel_congr
  intro a
  have hrep := repair_equiv (snapshotBlowup x) (snapshotBlowup y)
    (cliqueVertexRename (2*m) φ) _ _ (snapshotBlowup_rename φ ψ flip he)
    (snapshotCandidates_rename pack A W T φ ψ flip he) (x.root,a)
  simpa only [hr,cliqueVertexRename,Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map] using hrep.symm

def localAnonymousRule : AnonymousRule V E (2*m) Unit :=
  Quot.lift (snapshotRepairedLabel pack A W T) (fun _ _ h =>
    snapshotRepairedLabel_rename pack A W T h)

end
end MISLocal


/- ===== Source: MISLocal/SnapshotAgreement.lean ===== -/

/-! A snapshot contains every row and extracted ID whose incident skeleton
edges are visible. This is the concrete link from a quotient rule to the
single global repaired candidate set. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

theorem inBall_trans {V : Type*} (G : SimpleGraph V) {s t : ℕ} {v w u : V}
    (hvw : InBall G s v w) (hwu : InBall G t w u) : InBall G (s+t) v u := by
  induction t generalizing s w with
  | zero => simpa using hwu ▸ hvw
  | succ t ih =>
    rcases hwu with hwu | ⟨z,hwz,hzu⟩
    · subst u; exact inBall_mono G (by omega) hvw
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (inBall_append G s hvw hwz) hzu

theorem inBall_map_le {V : Type*} {G H : SimpleGraph V} (h : G ≤ H)
    (t : ℕ) (v u : V) (hb : InBall G t v u) : InBall H t v u := by
  induction t generalizing v u with
  | zero => exact hb
  | succ t ih =>
    rcases hb with he | ⟨w,hvw,hwu⟩
    · exact Or.inl he
    · exact Or.inr ⟨w,h hvw,ih w u hwu⟩

theorem inBall_local_rows {V : Type*} (G H : SimpleGraph V) (t : ℕ) (v u : V)
    (hrows : ∀ w, InBall G t v w → ∀ z, G.Adj w z ↔ H.Adj w z)
    (hb : InBall G t v u) : InBall H t v u := by
  induction t generalizing v u with
  | zero => exact hb
  | succ t ih =>
    rcases hb with he | ⟨w,hvw,hwu⟩
    · exact Or.inl he
    · exact Or.inr ⟨w,(hrows v (inBall_self G (t+1) v) w).mp hvw,
        ih w u (fun z hz => hrows z (Or.inr ⟨w,hvw,hz⟩)) hwu⟩

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}

def edgeSnapshot (M : G.edgeSet → EdgeMatrix k) (S : Finset G.edgeSet) (v : V) :
    NamedLocalView V G.edgeSet k Unit where
  root := v
  coin := ()
  edges e := if e ∈ S then some (edgeLeft G e,edgeRight G e,M e) else none

def fullEdgeSnapshot (M : G.edgeSet → EdgeMatrix k) (v : V) :
    NamedLocalView V G.edgeSet k Unit := edgeSnapshot G M Finset.univ v

omit [Fintype V] [DecidableRel G.Adj] in
theorem snapshotSkeleton_le (M : G.edgeSet → EdgeMatrix k) (S : Finset G.edgeSet) (v : V) :
    snapshotSkeleton (edgeSnapshot G M S v) ≤ G := by
  rintro a b ⟨_,e,z,he,hz⟩
  have hes : e ∈ S := by
    by_contra hn
    simp [edgeSnapshot,hn] at he
  have hez : (edgeLeft G e,edgeRight G e,M e) = z := by
    simpa [edgeSnapshot,hes] using he
  subst z
  rcases hz with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [← ha,← hb]; exact endpoint_adj G e
  · rw [← ha,← hb]; exact (endpoint_adj G e).symm

theorem fullSnapshotSkeleton (M : G.edgeSet → EdgeMatrix k) (v : V) :
    snapshotSkeleton (fullEdgeSnapshot G M v) = G := by
  apply le_antisymm (snapshotSkeleton_le G M Finset.univ v)
  intro a b hab
  let e : G.edgeSet := ⟨s(a,b),hab⟩
  have hp : s(edgeLeft G e,edgeRight G e) = s(a,b) := edge_endpoints G e
  refine ⟨hab.ne,e,(edgeLeft G e,edgeRight G e,M e),?_,?_⟩
  · simp [fullEdgeSnapshot,edgeSnapshot]
  · rcases Sym2.eq_iff.mp hp with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2,h.1⟩

theorem fullSnapshotBlowup (M : G.edgeSet → EdgeMatrix k) (v : V) :
    snapshotBlowup (fullEdgeSnapshot G M v) = cliqueBlowup G M := by
  ext x y
  constructor
  · rintro (h | ⟨_,e,z,he,hz⟩)
    · exact Or.inl h
    · have hez : (edgeLeft G e,edgeRight G e,M e) = z := by
        simpa [fullEdgeSnapshot,edgeSnapshot] using he
      subst z
      exact Or.inr ⟨e,hz⟩
  · rintro (h | ⟨e,hz⟩)
    · exact Or.inl h
    · have ha := crossCliqueAdj_skeleton G M (show crossCliqueAdj G M x y from ⟨e,hz⟩)
      exact Or.inr ⟨ha.ne,e,(edgeLeft G e,edgeRight G e,M e),
        by simp [fullEdgeSnapshot,edgeSnapshot],hz⟩

theorem snapshotSkeleton_row (M : G.edgeSet → EdgeMatrix k) (S : Finset G.edgeSet)
    (root v : V) (hsee : ∀ e, edgeIncident (edgeLeft G) (edgeRight G) v e → e ∈ S) (w : V) :
    (snapshotSkeleton (edgeSnapshot G M S root)).Adj v w ↔ G.Adj v w := by
  constructor
  · exact fun h => snapshotSkeleton_le G M S root h
  · intro hvw
    have ha : (snapshotSkeleton (fullEdgeSnapshot G M root)).Adj v w := by
      rw [fullSnapshotSkeleton G M root]; exact hvw
    obtain ⟨hne,e,z,he,hz⟩ := ha
    have hez : (edgeLeft G e,edgeRight G e,M e) = z := by
      simpa [fullEdgeSnapshot,edgeSnapshot] using he
    subst z
    have hi : edgeIncident (edgeLeft G) (edgeRight G) v e :=
      hz.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    exact ⟨hne,e,(edgeLeft G e,edgeRight G e,M e),by simp [edgeSnapshot,hsee e hi],hz⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem snapshotBlowup_row (M : G.edgeSet → EdgeMatrix k) (S : Finset G.edgeSet)
    (root : V) (v : V × Fin k)
    (hsee : ∀ e, edgeIncident (edgeLeft G) (edgeRight G) v.1 e → e ∈ S)
    (w : V × Fin k) :
    (snapshotBlowup (edgeSnapshot G M S root)).Adj v w ↔ (cliqueBlowup G M).Adj v w := by
  constructor
  · rintro (h | ⟨_,e,z,he,hz⟩)
    · exact Or.inl h
    · have hes : e ∈ S := by by_contra hn; simp [edgeSnapshot,hn] at he
      have hez : (edgeLeft G e,edgeRight G e,M e) = z := by simpa [edgeSnapshot,hes] using he
      subst z
      exact Or.inr ⟨e,hz⟩
  · rintro (h | ⟨e,hz⟩)
    · exact Or.inl h
    · have hi : edgeIncident (edgeLeft G) (edgeRight G) v.1 e :=
        hz.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      have ha := crossCliqueAdj_skeleton G M (show crossCliqueAdj G M v w from ⟨e,hz⟩)
      exact Or.inr ⟨ha.ne,e,(edgeLeft G e,edgeRight G e,M e),
        by simp [edgeSnapshot,hsee e hi],hz⟩

omit [DecidableEq V] in
theorem ball_incident_seen {r : ℕ} {root v : V} (hb : InBall G r root v)
    (e : G.edgeSet) (hi : edgeIncident (edgeLeft G) (edgeRight G) v e) :
    e ∈ seen G (r+1) root :=
  (seen_ball G r root e).mpr ⟨v,(incident_iff_mem G v e).mp hi,hb⟩

theorem snapshotBlockStrings_agrees {m : ℕ} (M : G.edgeSet → EdgeMatrix (2*m))
    (S : Finset G.edgeSet) (root v : V)
    (hsee : ∀ e, edgeIncident (edgeLeft G) (edgeRight G) v e → e ∈ S) :
    snapshotBlockStrings m (edgeSnapshot G M S root) v =
      snapshotBlockStrings m (fullEdgeSnapshot G M root) v := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ S
  · simp [edgeSnapshot,fullEdgeSnapshot,he]
  · have hl : edgeLeft G e ≠ v := fun h => he (hsee e (Or.inl h))
    have hr : edgeRight G e ≠ v := fun h => he (hsee e (Or.inr h))
    funext p
    simp [edgeSnapshot,fullEdgeSnapshot,he,datumBlockString,hl,hr]

theorem fullSnapshotBlockStrings {m : ℕ} (M : G.edgeSet → EdgeMatrix (2*m)) (root v : V) :
    snapshotBlockStrings m (fullEdgeSnapshot G M root) v = extractedBlockStrings G m M v := by
  funext p
  simp only [snapshotBlockStrings,fullEdgeSnapshot,edgeSnapshot,Finset.mem_univ,if_true,
    Option.elim_some,Finset.sum_apply,extractedBlockStrings,vertexBlockSum,AddMonoidHom.comp_apply,
    endpointSum,blockRestriction,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Fintype.sum_prod_type,
    Fintype.sum_bool,outgoingEndpoint,if_true,Bool.false_eq_true,if_false,matrixBitGroupEquiv,
    datumBlockString,Pi.zero_apply]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.sum_apply,Pi.zero_apply,Pi.add_apply]
  by_cases hl : edgeLeft G e = v <;> by_cases hr : edgeRight G e = v <;>
    simp [hl,hr,matrixBitGroupEquiv,add_comm]

theorem fullSnapshotIdentifiers {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (M : G.edgeSet → EdgeMatrix (2*m)) (root : V) :
    snapshotIdentifiers pack (fullEdgeSnapshot G M root) = extractedIdentifiers G pack M := by
  funext va
  unfold snapshotIdentifiers
  rw [fullSnapshotBlockStrings G M root va.1]
  rfl

theorem snapshotIdentifiers_agrees {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (M : G.edgeSet → EdgeMatrix (2*m)) (S : Finset G.edgeSet) (root : V)
    (va : V × Fin (2*m))
    (hsee : ∀ e, edgeIncident (edgeLeft G) (edgeRight G) va.1 e → e ∈ S) :
    snapshotIdentifiers pack (edgeSnapshot G M S root) va =
      snapshotIdentifiers pack (fullEdgeSnapshot G M root) va := by
  unfold snapshotIdentifiers
  rw [snapshotBlockStrings_agrees G M S root va.1 hsee]

theorem snapshot_ball_agrees (M : G.edgeSet → EdgeMatrix k) (R c s : ℕ) (root v u : V)
    (hc : InBall G c root v) (hcs : c+s ≤ R) :
    InBall (snapshotSkeleton (edgeSnapshot G M (seen G (R+1) root) root)) s v u ↔
      InBall G s v u := by
  constructor
  · exact inBall_map_le (snapshotSkeleton_le G M (seen G (R+1) root) root) s v u
  · apply inBall_local_rows G _ s v u
    intro w hw z
    exact (snapshotSkeleton_row G M (seen G (R+1) root) root w
      (fun e he => ball_incident_seen G (inBall_mono G hcs (inBall_trans G hc hw)) e he) z).symm

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/LocalBallCounts.lean ===== -/

/-! Elementary ball-size bounds, with no truncated subtraction. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

def ballFinset (t : ℕ) (v : V) : Finset V := Finset.univ.filter (InBall G t v)

omit [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_ballFinset (t : ℕ) (v w : V) :
    w ∈ ballFinset G t v ↔ InBall G t v w := by simp [ballFinset]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem ballFinset_zero (v : V) : ballFinset G 0 v = {v} := by
  ext w; simp [InBall]

theorem ballFinset_succ (t : ℕ) (v : V) :
    ballFinset G (t+1) v = insert v ((G.neighborFinset v).biUnion (ballFinset G t)) := by
  ext w
  simp [InBall]

theorem ballFinset_card_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (t : ℕ) (v : V) :
    (ballFinset G t v).card ≤ (D+1)^t := by
  induction t generalizing v with
  | zero => simp [ballFinset_zero G v]
  | succ t ih =>
    rw [ballFinset_succ G t v]
    have hsum : (∑ w ∈ G.neighborFinset v, (ballFinset G t w).card) ≤ D*(D+1)^t := by
      calc
        _ ≤ ∑ _w ∈ G.neighborFinset v, (D+1)^t := Finset.sum_le_sum (fun w _ => ih w)
        _ = G.degree v * (D+1)^t := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ (hD v)
    have hp : 1 ≤ (D+1)^t := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ ((G.neighborFinset v).biUnion (ballFinset G t)).card+1 := Finset.card_insert_le _ _
      _ ≤ D*(D+1)^t+1 := Nat.add_le_add_right ((Finset.card_biUnion_le).trans hsum) _
      _ ≤ (D+1)^(t+1) := by rw [pow_succ]; nlinarith

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem cliqueBall_card {k t : ℕ} (v : V) :
    Fintype.card {z : V × Fin k // InBall G t v z.1} = (ballFinset G t v).card*k := by
  let e : {z : V × Fin k // InBall G t v z.1} ≃
      {w : V // w ∈ ballFinset G t v} × Fin k :=
    { toFun z := (⟨z.val.1,(mem_ballFinset G t v z.val.1).mpr z.property⟩,z.val.2)
      invFun z := ⟨(z.1.val,z.2),(mem_ballFinset G t v z.1.val).mp z.1.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr e,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin]

end
end MISLocal


/- ===== Source: MISLocal/ExtractedCollisions.lean ===== -/

/-! Apply the proved joint distribution, rather than assume independence of
the tentative IDs. Difference of two coordinates is uniform in the bit group. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

def coordinateDifference {I A : Type*} [AddCommGroup A] (i j : I) : (I → A) →+ A where
  toFun x := x i-x j
  map_zero' := by simp
  map_add' := by intros; simp; abel

theorem coordinateDifference_surjective {I A : Type*} [AddCommGroup A]
    {i j : I} (hij : i ≠ j) : Function.Surjective (coordinateDifference (A := A) i j) := by
  intro a
  refine ⟨Function.update (fun _ => 0) i a,?_⟩
  simp [coordinateDifference,hij.symm]

namespace FiniteProb

theorem uniform_point {A : Type*} [Fintype A] [Nonempty A] (a : A) :
    (uniform A).prob (fun x => x = a) = (Fintype.card A : ℝ)⁻¹ := by
  simp [prob,expect,uniform,bit]

theorem uniform_group_collision {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] [AddCommGroup A] {i j : I} (hij : i ≠ j) :
    (uniform (I → A)).prob (fun x => x i = x j) = (Fintype.card A : ℝ)⁻¹ := by
  have hd := uniform_map_surjective_addHom (coordinateDifference (A := A) i j)
    (coordinateDifference_surjective hij)
  have hp := congrArg (fun μ : FiniteProb A => μ.prob (fun a => a = 0)) hd
  dsimp only at hp
  rw [prob_map,uniform_point] at hp
  simpa only [coordinateDifference,AddMonoidHom.coe_mk,ZeroHom.coe_mk,sub_eq_zero] using hp

theorem uniform_identifier_collision {I : Type*} [Fintype I] [DecidableEq I] (b : ℕ)
    {i j : I} (hij : i ≠ j) :
    (uniform (I → Fin (2^b))).prob (fun x => x i = x j) = 1/(2^b : ℕ) := by
  have hm := uniform_map_equiv (wordsIdentifierEquiv (X := I) b)
  have hp := congrArg (fun μ : FiniteProb (I → Fin (2^b)) => μ.prob (fun x => x i = x j)) hm
  dsimp only at hp
  rw [prob_map] at hp
  have he (x : I → Fin b → ZMod 2) :
      wordsIdentifierEquiv b x i = wordsIdentifierEquiv b x j ↔ x i = x j :=
    (wordIdentifierEquiv b).injective.eq_iff
  rw [prob_congr _ he,uniform_group_collision hij] at hp
  rw [← hp]
  simp [ZMod.card,one_div]

end FiniteProb

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))

theorem extractedIdentifier_collision (hdegree : ∀ v, 0 < G.degree v)
    {x y : V × Fin (2*m)} (hxy : x ≠ y) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))).prob
      (fun M => extractedIdentifiers G pack M x = extractedIdentifiers G pack M y) = 1/(2^b : ℕ) := by
  have hp := congrArg (fun μ : FiniteProb ((V × Fin (2*m)) → Fin (2^b)) =>
    μ.prob (fun ids => ids x = ids y)) (extractedIdentifiers_jointly_uniform G pack hdegree)
  dsimp only at hp
  rw [FiniteProb.prob_map,FiniteProb.uniform_identifier_collision b hxy] at hp
  exact hp

theorem extracted_local_collision_bound (hdegree : ∀ v, 0 < G.degree v)
    (t : ℕ) (root : V) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m)))).prob
      (fun M => ¬Set.InjOn (extractedIdentifiers G pack M) {z | InBall G t root z.1}) ≤
      ((ballFinset G t root).card*(2*m) : ℕ) *
        (((ballFinset G t root).card*(2*m) : ℕ) - (1:ℝ)) / (2^b : ℕ) := by
  let I := {z : V × Fin (2*m) // InBall G t root z.1}
  have hn : 0 < 2^b := by positivity
  have hi := local_collision_bound
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin (2*m) × Fin (2*m))))
    (fun i : I => fun M => extractedIdentifiers G pack M i.val) (2^b) hn
    (fun i j hij => by
      rw [extractedIdentifier_collision G pack hdegree (fun h => hij (Subtype.ext h))]
      have hp : (0:ℝ) < (2^b : ℕ) := by positivity
      exact div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) hp.le)
  have he (M : G.edgeSet → EdgeMatrix (2*m)) :
      Function.Injective (fun i : I => extractedIdentifiers G pack M i.val) ↔
        Set.InjOn (extractedIdentifiers G pack M) {z | InBall G t root z.1} := by
    constructor
    · intro h x hx y hy hxy
      exact congrArg Subtype.val (h (show extractedIdentifiers G pack M (⟨x,hx⟩ : I) =
        extractedIdentifiers G pack M (⟨y,hy⟩ : I) from hxy))
    · intro h x y hxy
      exact Subtype.ext (h x.property y.property hxy)
  rw [FiniteProb.prob_congr _ (fun M => not_congr (he M)),cliqueBall_card G root] at hi
  exact hi

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/SnapshotLocality.lean ===== -/

/-! A radius-(T+3) snapshot gives exactly the global candidate and repair
decisions at its root. This agreement is proved before invoking occupancy. -/

open scoped Classical
namespace MISLocal
noncomputable section

theorem repair_local_graph {X : Type*} (G H : SimpleGraph X) (S S' : Set X) (v : X)
    (hrow : ∀ w, G.Adj v w ↔ H.Adj v w) (hv : v ∈ S ↔ v ∈ S')
    (hn : ∀ w, G.Adj v w → (w ∈ S ↔ w ∈ S')) :
    v ∈ repair G S ↔ v ∈ repair H S' := by
  constructor
  · rintro ⟨hs,hns⟩
    refine ⟨hv.mp hs,fun w hw hsw => ?_⟩
    have hg := (hrow w).mpr hw
    exact hns w hg ((hn w hg).mpr hsw)
  · rintro ⟨hs,hns⟩
    exact ⟨hv.mpr hs,fun w hw hsw => hns w ((hrow w).mp hw) ((hn w hw).mp hsw)⟩

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m b : ℕ} (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    {Tape State : Type*} (A : UniformLocalProtocol (2^b) Tape State)
    (W : Fin (2^b) → Tape) (T : ℕ)

theorem snapshotUnique_agrees (M : G.edgeSet → EdgeMatrix (2*m)) (R c : ℕ) (root v : V)
    (hc : InBall G c root v) (hR : c+(T+1) ≤ R) :
    snapshotUnique pack T (edgeSnapshot G M (seen G (R+1) root) root) v ↔
      snapshotUnique pack T (fullEdgeSnapshot G M root) v := by
  let x := edgeSnapshot G M (seen G (R+1) root) root
  let y := fullEdgeSnapshot G M root
  have hb (z : V × Fin (2*m)) :
      InBall (snapshotSkeleton x) (T+1) v z.1 ↔ InBall (snapshotSkeleton y) (T+1) v z.1 := by
    dsimp [x,y]
    rw [fullSnapshotSkeleton G M root]
    exact snapshot_ball_agrees G M R c (T+1) root v z.1 hc hR
  have hi (z : V × Fin (2*m)) (hz : InBall (snapshotSkeleton y) (T+1) v z.1) :
      snapshotIdentifiers pack x z = snapshotIdentifiers pack y z := by
    rw [fullSnapshotSkeleton G M root] at hz
    exact snapshotIdentifiers_agrees G pack M _ root z (fun e he =>
      ball_incident_seen G (inBall_mono G hR (inBall_trans G hc hz)) e he)
  constructor
  · intro hu z hz w hw he
    apply hu ((hb z).mpr hz) ((hb w).mpr hw)
    rw [hi z hz,hi w hw]
    exact he
  · intro hu z hz w hw he
    apply hu ((hb z).mp hz) ((hb w).mp hw)
    rw [← hi z ((hb z).mp hz),← hi w ((hb w).mp hw)]
    exact he

theorem snapshotCandidates_agrees (M : G.edgeSet → EdgeMatrix (2*m)) (R c : ℕ)
    (root : V) (z : V × Fin (2*m)) (hc : InBall G c root z.1) (hR : c+(T+1) ≤ R) :
    z ∈ snapshotCandidates pack A W T (edgeSnapshot G M (seen G (R+1) root) root) ↔
      z ∈ snapshotCandidates pack A W T (fullEdgeSnapshot G M root) := by
  apply and_congr (snapshotUnique_agrees G pack T M R c root z.1 hc hR)
  let H := cliqueBlowup G M
  let x := edgeSnapshot G M (seen G (R+1) root) root
  let y := fullEdgeSnapshot G M root
  have hi (u : V × Fin (2*m)) (hu : InBall H (T+1) z u) :
      snapshotIdentifiers pack y u = snapshotIdentifiers pack x u := by
    exact (snapshotIdentifiers_agrees G pack M _ root u (fun e he =>
      ball_incident_seen G (inBall_mono G hR (inBall_trans G hc
        (blowup_ball_skeleton G M (T+1) z u hu))) e he)).symm
  have hr (u : V × Fin (2*m)) (hu : InBall H T z u) (w : V × Fin (2*m)) :
      H.Adj u w ↔ (snapshotBlowup x).Adj u w := by
    apply Iff.symm
    apply snapshotBlowup_row G M _ root u
    intro e he
    exact ball_incident_seen G (inBall_mono G (by omega) (inBall_trans G hc
      (blowup_ball_skeleton G M T z u hu))) e he
  have h := A.candidates_transport H (snapshotBlowup x) (Equiv.refl _)
    (snapshotIdentifiers pack y) (snapshotIdentifiers pack x) W T z hi hr
  dsimp only [H] at h
  rw [← fullSnapshotBlowup G M root] at h
  exact h.symm

theorem snapshotRepair_agrees (M : G.edgeSet → EdgeMatrix (2*m)) (root : V) (a : Fin (2*m)) :
    (root,a) ∈ repair (snapshotBlowup (edgeSnapshot G M (seen G (T+3) root) root))
      (snapshotCandidates pack A W T (edgeSnapshot G M (seen G (T+3) root) root)) ↔
    (root,a) ∈ repair (cliqueBlowup G M)
      (snapshotCandidates pack A W T (fullEdgeSnapshot G M root)) := by
  apply repair_local_graph
  · intro w
    exact snapshotBlowup_row G M _ root (root,a)
      (fun e he => ball_incident_seen G (inBall_self G (T+2) root) e he) w
  · exact snapshotCandidates_agrees G pack A W T M (T+2) 0 root (root,a) rfl (by omega)
  · intro w hw
    have ha : (cliqueBlowup G M).Adj (root,a) w :=
      (snapshotBlowup_row G M _ root (root,a)
        (fun e he => ball_incident_seen G (inBall_self G (T+2) root) e he) w).mp hw
    have hb : InBall G 1 root w.1 := by
      rcases blowup_adj_skeleton G M ha with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨w.1,h,rfl⟩
    exact snapshotCandidates_agrees G pack A W T M (T+2) 1 root w hb (by omega)

theorem snapshotCandidates_root_irrelevant (M : G.edgeSet → EdgeMatrix (2*m)) (v w : V) :
    snapshotCandidates pack A W T (fullEdgeSnapshot G M v) =
      snapshotCandidates pack A W T (fullEdgeSnapshot G M w) := rfl

theorem localAnonymousRule_representation
    (ω : ∀ i, matrixPrivateType G (2*m) (fun _ => Unit) i) (root : V) :
    runAnonymous G (localAnonymousRule pack A W T) (T+3) root ω =
      repairedLabel G (fun e => ω (Sum.inl e))
        (snapshotCandidates pack A W T (fullEdgeSnapshot G (fun e => ω (Sum.inl e)) root)) root := by
  change snapshotRepairedLabel pack A W T (namedLocalView G (T+3) root ω) = _
  have hv : namedLocalView G (T+3) root ω =
      edgeSnapshot G (fun e => ω (Sum.inl e)) (seen G (T+3) root) root := by
    have hc : ω (Sum.inr root) = () := @Subsingleton.elim Unit _ _ _
    simp only [namedLocalView,edgeSnapshot,hc]
  rw [hv]
  apply chooseLabel_congr
  exact snapshotRepair_agrees G pack A W T _ root

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/BlowupIDCompletion.lean ===== -/

/-! Legalize tentative IDs on the actual blow-up vertex set. The completion
is a genuine bijection and preserves the local IDs and ID-indexed tapes. -/

open scoped Classical
namespace MISLocal
noncomputable section

def completeVertexIDs {X : Type*} {n : ℕ} (enumeration : X ≃ Fin n)
    (U : Set X) (ids : X → Fin n) : X ≃ Fin n :=
  enumeration.trans (completeIDs {i | enumeration.symm i ∈ U}
    (fun i => ids (enumeration.symm i)))

theorem completeVertexIDs_agrees {X : Type*} {n : ℕ} (enumeration : X ≃ Fin n)
    (U : Set X) (ids : X → Fin n) (hinj : Set.InjOn ids U) (x : X) (hx : x ∈ U) :
    completeVertexIDs enumeration U ids x = ids x := by
  have hi : Set.InjOn (fun i => ids (enumeration.symm i)) {i | enumeration.symm i ∈ U} := by
    intro i hi j hj hij
    exact enumeration.symm.injective (hinj hi hj hij)
  change completeIDs _ _ (enumeration x) = _
  have ha := completeIDs_agrees {i | enumeration.symm i ∈ U}
    (fun i => ids (enumeration.symm i)) hi (enumeration x) (by simpa using hx)
  simpa only [enumeration.symm_apply_apply] using ha

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {m b : ℕ} (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (enumeration : (V × Fin (2*m)) ≃ Fin (2^b))
    {Tape State : Type*} (A : UniformLocalProtocol (2^b) Tape State)
    (W : Fin (2^b) → Tape) (T : ℕ)

def locallyUniqueIDs (root : V) (M : G.edgeSet → EdgeMatrix (2*m)) : Prop :=
  Set.InjOn (extractedIdentifiers G pack M) {z | InBall G (T+2) root z.1}

def completedBlowupIDs (root : V) (M : G.edgeSet → EdgeMatrix (2*m)) :
    (V × Fin (2*m)) ≃ Fin (2^b) :=
  completeVertexIDs enumeration {z | InBall G (T+2) root z.1} (extractedIdentifiers G pack M)

omit [DecidableEq V] in
theorem completedBlowupIDs_agrees (root : V) (M : G.edgeSet → EdgeMatrix (2*m))
    (h : locallyUniqueIDs G pack T root M) (z : V × Fin (2*m))
    (hz : InBall G (T+2) root z.1) :
    completedBlowupIDs G pack enumeration T root M z = extractedIdentifiers G pack M z :=
  completeVertexIDs_agrees enumeration _ _ h z hz

/-- At the root and each adjacent clique, the collision-gated candidate
equals the actual execution on the legal completed ID assignment. -/
theorem completed_candidate_simulation (root : V) (M : G.edgeSet → EdgeMatrix (2*m))
    (h : locallyUniqueIDs G pack T root M) (z : V × Fin (2*m))
    (hz : InBall G 1 root z.1) :
    z ∈ snapshotCandidates pack A W T (fullEdgeSnapshot G M root) ↔
      z ∈ A.candidates (cliqueBlowup G M)
        (completedBlowupIDs G pack enumeration T root M) W T := by
  have hc (u : V × Fin (2*m)) (hu : InBall G (T+1) z.1 u.1) :
      InBall G (T+2) root u.1 := by
    simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using inBall_trans G hz hu
  have hu : snapshotUnique pack T (fullEdgeSnapshot G M root) z.1 := by
    unfold snapshotUnique
    rw [fullSnapshotIdentifiers G pack M root,fullSnapshotSkeleton G M root]
    exact fun u huu v hvv huv => h (hc u huu) (hc v hvv) huv
  change (_ ∧ _) ↔ _
  simp only [hu,true_and]
  rw [fullSnapshotIdentifiers G pack M root,fullSnapshotBlowup G M root]
  apply A.candidates_local
  intro u huu
  exact (completedBlowupIDs_agrees G pack enumeration T root M h u
    (hc u (blowup_ball_skeleton G M (T+1) z u huu))).symm

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/MatrixUnitProbability.lean ===== -/

/-! Erasing the dummy private Unit coordinates gives precisely the original
independent fair-matrix sample space used in the concrete collision proofs. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)

def matrixUnitEquiv : (G.edgeSet → EdgeMatrix k) ≃
    (∀ i, matrixPrivateType G k (fun _ => Unit) i) where
  toFun M i := match i with
    | Sum.inl e => M e
    | Sum.inr _ => ()
  invFun ω e := ω (Sum.inl e)
  left_inv M := rfl
  right_inv ω := by
    funext i
    cases i with
    | inl e => rfl
    | inr v => exact @Subsingleton.elim Unit _ _ _

theorem matrixUnitProbability_map :
    (FiniteProb.pi (matrixPrivateProbability G k (fun _ => FiniteProb.uniform Unit))).map
      (matrixUnitEquiv G k).symm =
      FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k)) := by
  ext M
  rw [FiniteProb.map_equiv_weight]
  change (∏ i : G.edgeSet ⊕ V,
    (matrixPrivateProbability G k (fun _ => FiniteProb.uniform Unit) i).weight
      (matrixUnitEquiv G k M i)) = _
  rw [Fintype.prod_sum_type]
  simp only [matrixPrivateProbability,FiniteProb.sumProb,matrixUnitEquiv,Equiv.coe_fn_mk,
    Sum.elim_inl,Sum.elim_inr,FiniteProb.uniform,Fintype.card_unit,Nat.cast_one,inv_one,
    Finset.prod_const_one,mul_one]
  rfl

theorem matrixUnitProbability_prob (P : (G.edgeSet → EdgeMatrix k) → Prop) :
    (FiniteProb.pi (matrixPrivateProbability G k (fun _ => FiniteProb.uniform Unit))).prob
      (fun ω => P (fun e => ω (Sum.inl e))) =
      (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k))).prob P := by
  have h := congrArg (fun μ : FiniteProb (G.edgeSet → EdgeMatrix k) => μ.prob P)
    (matrixUnitProbability_map G k)
  dsimp only at h
  rw [FiniteProb.prob_map] at h
  exact h

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/ConcreteOccupancyReduction.lean ===== -/

/-! Invoke the occupancy theorem on the constructed LOCAL simulation.
Neither anonymity nor zero conflict nor radius is supplied as a hypothesis. -/

open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    {Tape State : Type*} (A : UniformLocalProtocol (2^b) Tape State)
    (W : Fin (2^b) → Tape) (T : ℕ)

theorem localAnonymousRule_noConflict (e : G.edgeSet)
    (ω : ∀ i, matrixPrivateType G (2*m) (fun _ => Unit) i) :
    ¬selectedConflict (fun M a b => M (a,b)=true)
      (ω (Sum.inl e),runAnonymous G (localAnonymousRule pack A W T) (T+3) (edgeLeft G e) ω,
        runAnonymous G (localAnonymousRule pack A W T) (T+3) (edgeRight G e) ω) := by
  rw [localAnonymousRule_representation G pack A W T ω (edgeLeft G e),
    localAnonymousRule_representation G pack A W T ω (edgeRight G e),
    snapshotCandidates_root_irrelevant G pack A W T _ (edgeRight G e) (edgeLeft G e)]
  exact repairedLabel_noConflict G _ _ e

variable [Nonempty V]

theorem concrete_fixed_table_occupancy {d : ℕ}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (T+3))).IsTree) (e : G.edgeSet)
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ 2*m)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log ((2*m:ℕ):ℝ))
    (hupper : Real.log ((2*m:ℕ):ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G (2*m) (fun _ => FiniteProb.uniform Unit))).prob
      (fun ω => Occupies (vertexClique (edgeLeft G e))
        (repair (cliqueBlowup G (fun i => ω (Sum.inl i)))
          (snapshotCandidates pack A W T
            (fullEdgeSnapshot G (fun i => ω (Sum.inl i)) (edgeLeft G e))))) ≤
      occupancyCap (T+3) ((d+1:ℕ):ℝ) := by
  have hz : (FiniteProb.pi (matrixPrivateProbability G (2*m) (fun _ => FiniteProb.uniform Unit))).prob
      (fun ω => selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e),runAnonymous G (localAnonymousRule pack A W T) (T+3) (edgeLeft G e) ω,
          runAnonymous G (localAnonymousRule pack A W T) (T+3) (edgeRight G e) ω)) = 0 := by
    simp only [FiniteProb.prob,FiniteProb.expect,bit,
      if_neg (localAnonymousRule_noConflict G pack A W T e _),mul_zero,Finset.sum_const_zero]
  have h := anonymous_graph_occupancy G (n := T+2) hreg ht (FiniteProb.uniform Unit)
    (localAnonymousRule pack A W T) e hz hD hk hlower hupper
  rw [FiniteProb.prob_congr _ (fun ω => by
    rw [localAnonymousRule_representation G pack A W T ω (edgeLeft G e),
      repairedLabel_occupies G])] at h
  exact h

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/FairBitProjection.lean ===== -/

/-! Fair bits stay jointly uniform under any injection of coordinate sets. -/

open scoped Classical
namespace MISLocal
noncomputable section

def bitVectorGroupEquiv (I : Type*) : (I → Bool) ≃ (I → ZMod 2) :=
  Equiv.piCongrRight (fun _ => bitGroupEquiv)

def coordinateRestriction {I J : Type*} (f : I ↪ J) : (J → ZMod 2) →+ (I → ZMod 2) where
  toFun x i := x (f i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coordinateRestriction_surjective {I J : Type*} (f : I ↪ J) :
    Function.Surjective (coordinateRestriction f) := by
  intro x
  refine ⟨Function.extend f x (fun _ => 0),?_⟩
  funext i
  exact f.injective.extend_apply x (fun _ => 0) i

namespace FiniteProb

theorem fairBits_map_restriction {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (f : I ↪ J) :
    (fairBits J).map (fun x => fun i => x (f i)) = fairBits I := by
  have hJ : fairBits J = uniform (J → Bool) := pi_uniform
  have hI : fairBits I = uniform (I → Bool) := pi_uniform
  rw [hJ,hI]
  calc
    _ = (((uniform (J → Bool)).map (bitVectorGroupEquiv J)).map
        (coordinateRestriction f)).map (bitVectorGroupEquiv I).symm := by
      rw [map_comp,map_comp]
      congr 1
      funext x i
      exact (bitGroupEquiv.symm_apply_apply (x (f i))).symm
    _ = _ := by
      rw [uniform_map_equiv,uniform_map_surjective_addHom _ (coordinateRestriction_surjective f),
        uniform_map_equiv]

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/FairRowDomination.lean ===== -/

/-! A fixed external choice must hit every independently sampled root row.
This estimate quantifies over fixed choices before seeing any matrix. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section
namespace FiniteProb

def curryBitEquiv (A B : Type*) : ((A × B) → Bool) ≃ (A → B → Bool) where
  toFun x a b := x (a,b)
  invFun x p := x p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem fairBits_row_hit {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    (fairBits (A × B)).prob (fun x => ∀ a, ∃ b, x (a,b) = true) =
      (1-(2:ℝ)^(-(Fintype.card B:ℤ)))^(Fintype.card A) := by
  have hfalse : (fairBits B).prob (fun x => ∀ b, x b = false) =
      (2:ℝ)^(-(Fintype.card B:ℤ)) := by
    have he (x : B → Bool) : (∀ b, x b = false) ↔ x = fun _ => false := by
      constructor
      · exact fun h => funext h
      · intro h b; simp only [h]
    rw [prob_congr _ he]
    have hu : fairBits B = uniform (B → Bool) := pi_uniform
    rw [hu,uniform_point]
    simp [zpow_neg,Fintype.card_fun]
  have hrow : (fairBits B).prob (fun x => ∃ b, x b = true) =
      1-(2:ℝ)^(-(Fintype.card B:ℤ)) := by
    have he (x : B → Bool) : (∃ b, x b = true) ↔ ¬(∀ b, x b = false) := by
      simp only [not_forall,Bool.not_eq_false]
    rw [prob_congr _ he,prob_not,hfalse]
  have hm : (fairBits (A × B)).map (curryBitEquiv A B) = pi (fun _ : A => fairBits B) := by
    have huAB : fairBits (A × B) = uniform ((A × B) → Bool) := pi_uniform
    have huB : fairBits B = uniform (B → Bool) := pi_uniform
    rw [huAB,uniform_map_equiv,huB,pi_uniform]
  have he (x : A → B → Bool) : bit (∀ a, ∃ b, x a b = true) =
      ∏ a, bit (∃ b, x a b = true) := by
    by_cases h : ∀ a, ∃ b, x a b = true
    · simp [bit,h]
    · obtain ⟨a,ha⟩ := not_forall.mp h
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (by simp [bit,ha])]
      simp [bit,h]
  have hp := congrArg (fun μ : FiniteProb (A → B → Bool) => μ.prob (fun x => ∀ a, ∃ b, x a b=true)) hm
  dsimp only at hp
  rw [prob_map] at hp
  change (fairBits (A × B)).prob (fun x => ∀ a, ∃ b, x (a,b)=true) = _ at hp
  rw [hp]
  change (pi (fun _ : A => fairBits B)).expect (fun x => bit (∀ a, ∃ b, x a b=true)) = _
  rw [expect_congr _ he,expect_pi_prod (fun _ : A => fairBits B)
    (fun _ row => bit (∃ b, row b=true))]
  change (∏ _a : A, (fairBits B).prob (fun x => ∃ b, x b=true)) = _
  simp [hrow]

theorem fixed_domination_probability {A B J : Type*} [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J] (f : (A × B) ↪ J)
    {D : ℕ} (hB : Fintype.card B ≤ D) :
    (fairBits J).prob (fun x => ∀ a, ∃ b, x (f (a,b))=true) ≤
      Real.exp (-(Fintype.card A:ℝ)*(2:ℝ)^(-(D:ℤ))) := by
  have hm := fairBits_map_restriction f
  have hp := congrArg (fun μ : FiniteProb ((A × B) → Bool) =>
    μ.prob (fun x => ∀ a, ∃ b, x (a,b)=true)) hm
  dsimp only at hp
  rw [prob_map,fairBits_row_hit] at hp
  rw [hp]
  have hq : (2:ℝ)^(-(D:ℤ)) ≤ (2:ℝ)^(-(Fintype.card B:ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
    exact neg_le_neg (by exact_mod_cast hB)
  have hn : 0 ≤ 1-(2:ℝ)^(-(Fintype.card B:ℤ)) := by
    have hu : (2:ℝ)^(-(Fintype.card B:ℤ)) ≤ (2:ℝ)^(0:ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    exact sub_nonneg.mpr (by simpa only [zpow_zero] using hu)
  have he : 1-(2:ℝ)^(-(Fintype.card B:ℤ)) ≤ Real.exp (-(2:ℝ)^(-(D:ℤ))) := by
    linarith [Real.add_one_le_exp (-(2:ℝ)^(-(D:ℤ)))]
  calc
    _ ≤ (Real.exp (-(2:ℝ)^(-(D:ℤ))))^(Fintype.card A) := pow_le_pow_left₀ hn he _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end FiniteProb
end
end MISLocal


/- ===== Source: MISLocal/CliqueDomination.lean ===== -/

/-! External domination of a clique is rare. One label is chosen in each
neighboring clique before applying the independent-row estimate, and then a
union bound includes every such choice, including matrix-dependent outputs. -/

open scoped BigOperators Classical
namespace MISLocal
noncomputable section

def flatMatrixEquiv (E : Type*) (k : ℕ) :
    (E → EdgeMatrix k) ≃ ((E × (Fin k × Fin k)) → Bool) where
  toFun M z := M z.1 z.2
  invFun x e p := x (e,p)
  left_inv _ := rfl
  right_inv _ := rfl

namespace FiniteProb
theorem fairMatrices_map_flat {E : Type*} [Fintype E] [DecidableEq E] (k : ℕ) :
    (pi (fun _ : E => fairBits (Fin k × Fin k))).map (flatMatrixEquiv E k) =
      fairBits (E × (Fin k × Fin k)) := by
  have hmatrix : fairBits (Fin k × Fin k) = uniform (EdgeMatrix k) := pi_uniform
  have hflat : fairBits (E × (Fin k × Fin k)) = uniform ((E × (Fin k × Fin k)) → Bool) := pi_uniform
  rw [hmatrix,pi_uniform,uniform_map_equiv,hflat]
end FiniteProb

namespace TreeGeometry
variable {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}

def neighborEdge (v : V) (w : G.neighborSet v) : G.edgeSet := ⟨s(v,w.val),w.property⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem neighborEdge_ends (v : V) (w : G.neighborSet v) :
    (edgeLeft G (neighborEdge G v w) = v ∧ edgeRight G (neighborEdge G v w) = w.val) ∨
      (edgeLeft G (neighborEdge G v w) = w.val ∧ edgeRight G (neighborEdge G v w) = v) :=
  Sym2.eq_iff.mp (edge_endpoints G (neighborEdge G v w))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem neighborEdge_injective (v : V) : Function.Injective (neighborEdge G v) := by
  intro w z h
  have he : s(v,w.val) = s(v,z.val) := congrArg Subtype.val h
  exact Subtype.ext (Sym2.congr_right.mp he)

def neighborPosition (v : V) (w : G.neighborSet v) (a b : Fin k) : Fin k × Fin k :=
  if edgeLeft G (neighborEdge G v w) = v then (a,b) else (b,a)

omit [Fintype V] [DecidableRel G.Adj] in
theorem adjacent_neighbor_entry (M : G.edgeSet → EdgeMatrix k) (v : V)
    (w : G.neighborSet v) (a b : Fin k)
    (h : (cliqueBlowup G M).Adj (v,a) (w.val,b)) :
    M (neighborEdge G v w) (neighborPosition G v w a b) = true := by
  rcases h with h | ⟨e,h⟩
  · exact False.elim (w.property.ne h.1)
  · have hi : edgeIncident (edgeLeft G) (edgeRight G) v e :=
      h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    have hw : edgeIncident (edgeLeft G) (edgeRight G) w.val e :=
      h.elim (fun h => Or.inr h.2.1) (fun h => Or.inl h.2.1)
    have he : e = neighborEdge G v w := Subtype.ext (edge_eq_of_incident G w.property.ne e hi hw)
    subst e
    rcases h with ⟨hl,_,hm⟩ | ⟨hr,hl,hm⟩
    · simpa [neighborPosition,hl] using hm
    · have hn : edgeLeft G (neighborEdge G v w) ≠ v := by
        intro heq
        exact (endpoint_adj G (neighborEdge G v w)).ne (heq.trans hr.symm)
      simpa [neighborPosition,hn] using hm

abbrev ActiveNeighbor {v : V} (f : G.neighborSet v → Option (Fin k)) :=
  {w : G.neighborSet v // ∃ b, f w = some b}

def activeLabel {v : V} (f : G.neighborSet v → Option (Fin k)) (w : ActiveNeighbor G f) : Fin k :=
  w.property.choose

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem activeLabel_spec {v : V} (f : G.neighborSet v → Option (Fin k)) (w : ActiveNeighbor G f) :
    f w.val = some (activeLabel G f w) := w.property.choose_spec

def neighborRowPosition {v : V} (f : G.neighborSet v → Option (Fin k))
    (z : Fin k × ActiveNeighbor G f) : G.edgeSet × (Fin k × Fin k) :=
  (neighborEdge G v z.2.val,neighborPosition G v z.2.val z.1 (activeLabel G f z.2))

omit [Fintype V] [DecidableRel G.Adj] in
theorem neighborRowPosition_injective {v : V} (f : G.neighborSet v → Option (Fin k)) :
    Function.Injective (neighborRowPosition G f) := by
  rintro ⟨a,w⟩ ⟨b,z⟩ h
  have he : neighborEdge G v w.val = neighborEdge G v z.val := congrArg Prod.fst h
  have hw : w = z := Subtype.ext ((neighborEdge_injective G v) he)
  subst z
  have hp := congrArg Prod.snd h
  change neighborPosition G v w.val a (activeLabel G f w) =
    neighborPosition G v w.val b (activeLabel G f w) at hp
  unfold neighborPosition at hp
  split_ifs at hp
  · have hab : a = b := congrArg (fun p : Fin k × Fin k => p.1) hp
    exact Prod.ext hab rfl
  · have hab : a = b := congrArg (fun p : Fin k × Fin k => p.2) hp
    exact Prod.ext hab rfl

def neighborRowEmbedding {v : V} (f : G.neighborSet v → Option (Fin k)) :
    (Fin k × ActiveNeighbor G f) ↪ (G.edgeSet × (Fin k × Fin k)) :=
  ⟨neighborRowPosition G f,neighborRowPosition_injective G f⟩

def choiceDominates {v : V} (f : G.neighborSet v → Option (Fin k))
    (M : G.edgeSet → EdgeMatrix k) : Prop :=
  ∀ a, ∃ w : ActiveNeighbor G f,
    M (neighborEdge G v w.val) (neighborPosition G v w.val a (activeLabel G f w)) = true

theorem choice_domination_probability (v : V) (f : G.neighborSet v → Option (Fin k)) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k))).prob
      (choiceDominates G f) ≤ Real.exp (-(k:ℝ)*(2:ℝ)^(-(G.degree v:ℤ))) := by
  have hc : Fintype.card (ActiveNeighbor G f) ≤ G.degree v := by
    have h := Fintype.card_le_of_injective (fun w : ActiveNeighbor G f => w.val) Subtype.val_injective
    simpa only [G.card_neighborSet_eq_degree] using h
  have h := FiniteProb.fixed_domination_probability (neighborRowEmbedding G f) hc
  have hm := FiniteProb.fairMatrices_map_flat (E := G.edgeSet) k
  have hp := congrArg (fun μ : FiniteProb ((G.edgeSet × (Fin k × Fin k)) → Bool) =>
    μ.prob (fun x => ∀ a, ∃ w : ActiveNeighbor G f, x (neighborRowEmbedding G f (a,w))=true)) hm
  dsimp only at hp
  rw [FiniteProb.prob_map] at hp
  rw [← hp] at h
  simpa only [Fintype.card_fin,neighborRowEmbedding,neighborRowPosition,flatMatrixEquiv,
    Equiv.coe_fn_mk,Function.Embedding.coeFn_mk] using h

omit [Fintype V] [DecidableRel G.Adj] in
theorem external_domination_has_choice (M : G.edgeSet → EdgeMatrix k) (v : V)
    (h : ExternallyDominatable (cliqueBlowup G M) (vertexClique v)) :
    ∃ f : G.neighborSet v → Option (Fin k), choiceDominates G f M := by
  obtain ⟨S,hS,hdis,hdom⟩ := h
  let f : G.neighborSet v → Option (Fin k) := fun w => chooseLabel (fun b => (w.val,b) ∈ S)
  refine ⟨f,fun a => ?_⟩
  obtain ⟨⟨w,b⟩,hwb,hadj⟩ := hdom (v,a) rfl
  have hwv : w ≠ v := by
    intro he
    exact Set.disjoint_left.mp hdis (show (w,b) ∈ vertexClique v from he) hwb
  have hsk : G.Adj v w :=
    (blowup_adj_skeleton G M hadj).resolve_left (Ne.symm hwv)
  let wn : G.neighborSet v := ⟨w,hsk⟩
  have hf : f wn = some b := by
    change chooseLabel (fun c => (w,c) ∈ S) = some b
    unfold chooseLabel
    have hp : ∃ c, (w,c) ∈ S := ⟨b,hwb⟩
    rw [dif_pos hp]
    apply congrArg some
    have heq := clique_independent_at_most_one (cliqueBlowup G M)
      (vertexClique_isClique G M w) hS (show (w,hp.choose) ∈ vertexClique w from rfl)
      hp.choose_spec (show (w,b) ∈ vertexClique w from rfl) hwb
    exact congrArg Prod.snd heq
  let wa : ActiveNeighbor G f := ⟨wn,⟨b,hf⟩⟩
  refine ⟨wa,?_⟩
  have he : activeLabel G f wa = b := Option.some.inj ((activeLabel_spec G f wa).symm.trans hf)
  rw [he]
  exact adjacent_neighbor_entry G M v wn a b hadj

theorem external_domination_probability (v : V) :
    (FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k))).prob
      (fun M => ExternallyDominatable (cliqueBlowup G M) (vertexClique v)) ≤
      ((k+1:ℕ):ℝ)^(G.degree v) * Real.exp (-(k:ℝ)*(2:ℝ)^(-(G.degree v:ℤ))) := by
  let μ := FiniteProb.pi (fun _ : G.edgeSet => FiniteProb.fairBits (Fin k × Fin k))
  calc
    _ ≤ μ.prob (fun M => ∃ f : G.neighborSet v → Option (Fin k), choiceDominates G f M) :=
      μ.prob_mono (fun M h => external_domination_has_choice G M v h)
    _ ≤ ∑ f : G.neighborSet v → Option (Fin k), μ.prob (choiceDominates G f) :=
      μ.prob_exists_le_sum _
    _ ≤ ∑ _f : G.neighborSet v → Option (Fin k),
        Real.exp (-(k:ℝ)*(2:ℝ)^(-(G.degree v:ℤ))) :=
      Finset.sum_le_sum (fun f _ => choice_domination_probability G v f)
    _ = _ := by simp [Fintype.card_fun,G.card_neighborSet_eq_degree]

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/ConcreteFiniteObstruction.lean ===== -/

/-! A concrete finite LOCAL obstruction. The collision and domination errors,
simulation, repaired representation, and per-fixed-table occupancy estimate
are all discharged. Correctness and measurability describe the supplied
randomized LOCAL program, rather than the desired lower bound. -/

open MeasureTheory
open scoped Classical
namespace MISLocal
noncomputable section

theorem repaired_occupancy_measurable {X W : Type*} [Fintype X] [MeasurableSpace W]
    (G : SimpleGraph X) (C : Set X) (S : W → Set X)
    (hS : ∀ x, MeasurableSet {w | x ∈ S w}) :
    MeasurableSet {w | Occupies C (repair G (S w))} := by
  have hr (x : X) : MeasurableSet {w | x ∈ repair G (S w)} := by
    apply (hS x).inter
    have hn (y : X) : MeasurableSet {w | G.Adj x y → y ∉ S w} := by
      by_cases hxy : G.Adj x y
      · simpa only [hxy,true_implies] using (hS y).compl
      · simp only [hxy,false_implies]
        exact MeasurableSet.univ
    simpa only [Set.iInter_setOf] using MeasurableSet.iInter hn
  change MeasurableSet {w | ∃ x, x ∈ C ∧ x ∈ repair G (S w)}
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ C
  · simpa only [hx,true_and] using hr x
  · simp only [hx,false_and]
    exact MeasurableSet.empty

namespace TreeGeometry
variable {V Tape State : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (enumeration : (V × Fin (2*m)) ≃ Fin (2^b))
    (A : UniformLocalProtocol (2^b) Tape State) [MeasurableSpace Tape]
    (ν : Measure (Fin (2^b) → Tape)) [IsProbabilityMeasure ν] (T : ℕ)

def localCollisionError (v : V) : ℝ :=
  (((ballFinset G (T+2) v).card*(2*m) : ℕ):ℝ) *
    ((((ballFinset G (T+2) v).card*(2*m) : ℕ):ℝ)-1) / ((2^b:ℕ):ℝ)

def localDominationError (D : ℕ) : ℝ :=
  ((2*m+1:ℕ):ℝ)^D * Real.exp (-((2*m:ℕ):ℝ)*(2:ℝ)^(-(D:ℤ)))

theorem concrete_finite_obstruction {d : ℕ}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (T+3))).IsTree) (e : G.edgeSet)
    (ε : ℝ) (hε : ε ≤ 1)
    (hcorrect : ∀ M : G.edgeSet → EdgeMatrix (2*m), 1-ε ≤ ν.real {W |
      Maximal (cliqueBlowup G M).IsIndepSet
        (A.candidates (cliqueBlowup G M)
          (completedBlowupIDs G pack enumeration T (edgeLeft G e) M) W T)})
    (hmeas : ∀ (M : G.edgeSet → EdgeMatrix (2*m)) (z : V × Fin (2*m)),
      MeasurableSet {W | z ∈ A.candidates (cliqueBlowup G M) (extractedIdentifiers G pack M) W T})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ 2*m)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log ((2*m:ℕ):ℝ))
    (hupper : Real.log ((2*m:ℕ):ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (1-ε)*(1-localCollisionError G (m := m) (b := b) T (edgeLeft G e)-
      localDominationError (m := m) (d+1)) ≤ occupancyCap (T+3) ((d+1:ℕ):ℝ) := by
  let μ := FiniteProb.pi (matrixPrivateProbability G (2*m) (fun _ => FiniteProb.uniform Unit))
  let matrix := fun ω : ∀ i, matrixPrivateType G (2*m) (fun _ => Unit) i => fun e => ω (Sum.inl e)
  let root := edgeLeft G e
  let H := fun ω => cliqueBlowup G (matrix ω)
  let S := fun ω W => snapshotCandidates pack A W T (fullEdgeSnapshot G (matrix ω) root)
  let out := fun ω W => A.candidates (H ω)
    (completedBlowupIDs G pack enumeration T root (matrix ω)) W T
  let unique := fun ω => locallyUniqueIDs G pack T root (matrix ω)
  apply finite_obstruction μ ν H (vertexClique root) out S unique ε
    (localCollisionError G (m := m) (b := b) T root)
    (localDominationError (m := m) (d+1)) _ hε
  · dsimp only [μ,unique,locallyUniqueIDs,matrix]
    rw [matrixUnitProbability_prob G (2*m)
      (fun M => ¬Set.InjOn (extractedIdentifiers G pack M) {z | InBall G (T+2) root z.1})]
    exact extracted_local_collision_bound G pack (by intro v; rw [hreg]; omega) (T+2) root
  · dsimp only [μ,H,matrix]
    rw [matrixUnitProbability_prob G (2*m)
      (fun M => ExternallyDominatable (cliqueBlowup G M) (vertexClique root))]
    have h := external_domination_probability G (k := 2*m) root
    rw [hreg root] at h
    exact h
  · exact fun ω => hcorrect (matrix ω)
  · intro ω hu W z hz w hw
    have hzroot : z.1 = root := hz
    have hb : InBall G 1 root w.1 := by
      rcases hw with hw | hw
      · exact Or.inl ((congrArg Prod.fst hw).trans hzroot)
      · rcases blowup_adj_skeleton G (matrix ω) hw with he | ha
        · exact Or.inl (he.symm.trans hzroot)
        · exact Or.inr ⟨w.1,hzroot ▸ ha,rfl⟩
    exact completed_candidate_simulation G pack enumeration A W T root (matrix ω) hu w hb
  · intro ω
    apply repaired_occupancy_measurable (H ω) (vertexClique root) (S ω)
    intro z
    by_cases hu : snapshotUnique pack T (fullEdgeSnapshot G (matrix ω) root) z.1
    · have h := hmeas (matrix ω) z
      simpa only [S,snapshotCandidates,Set.mem_setOf_eq,hu,true_and,
        fullSnapshotBlowup G (matrix ω) root,fullSnapshotIdentifiers G pack (matrix ω) root] using h
    · simp only [S,snapshotCandidates,Set.mem_setOf_eq,hu,false_and]
      exact MeasurableSet.empty
  · intro W
    exact concrete_fixed_table_occupancy G pack A W T hreg ht e hD hk hlower hupper

end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/PrefixTree.lean ===== -/

/-! Acyclicity from height and a unique lower neighbor, applied to prefix trees. -/
open scoped Classical
namespace MISLocal
noncomputable section
theorem acyclic_of_unique_lower_neighbor {V : Type*} (G : SimpleGraph V)
    (height : V → ℕ)
    (hstep : ∀ {v w}, G.Adj v w → height v + 1 = height w ∨ height w + 1 = height v)
    (hparent : ∀ {v x y}, G.Adj v x → G.Adj v y →
      height x < height v → height y < height v → x = y) : G.IsAcyclic := by
  intro v p hp
  obtain ⟨z,hz,hmax⟩ := p.support.toFinset.exists_max_image height ⟨v,by simp⟩
  have hz' : z ∈ p.support := List.mem_toFinset.mp hz
  let q := p.rotate hz'
  have hq : q.IsCycle := hp.rotate hz'
  have hbound (u : V) (hu : u ∈ q.support) : height u ≤ height z := by
    have hu' : u ∈ p.support := by
      have hsub := p.toSubgraph_rotate hz'
      have hmem : u ∈ q.toSubgraph.verts := by simpa using hu
      have hpvert : u ∈ p.toSubgraph.verts := by rw [← hsub]; exact hmem
      simpa using hpvert
    exact hmax u (List.mem_toFinset.mpr hu')
  have hs := hstep (SimpleGraph.Walk.adj_snd hq.not_nil)
  have ht := hstep (SimpleGraph.Walk.adj_penultimate hq.not_nil).symm
  have hsl : height q.snd < height z := by
    have := hbound q.snd (q.getVert_mem_support 1)
    rcases hs with hs | hs <;> omega
  have htl : height q.penultimate < height z := by
    have := hbound q.penultimate (q.getVert_mem_support (q.length-1))
    rcases ht with ht | ht <;> omega
  exact hq.snd_ne_penultimate
    (hparent (SimpleGraph.Walk.adj_snd hq.not_nil)
      (SimpleGraph.Walk.adj_penultimate hq.not_nil).symm hsl htl)
def prefixTree (α : Type*) : SimpleGraph (List α) where
  Adj v w := (∃ i, v = i::w) ∨ (∃ i, w = i::v)
  symm := by intro v w h; exact h.symm
  loopless := by
    intro w h
    rcases h with ⟨i,h⟩ | ⟨i,h⟩ <;>
      have he := congrArg List.length h <;> simp only [List.length_cons] at he <;> omega
theorem prefixTree_acyclic (α : Type*) : (prefixTree α).IsAcyclic := by
  apply acyclic_of_unique_lower_neighbor _ List.length
  · rintro v w (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro v x y hx hy hxl hyl
    rcases hx with ⟨i,hx⟩ | ⟨i,hx⟩
    · rcases hy with ⟨j,hy⟩ | ⟨j,hy⟩
      · exact (List.cons.inj (hx.symm.trans hy)).2
      · have he := congrArg List.length hy
        simp only [List.length_cons] at he
        omega
    · have he := congrArg List.length hx
      simp only [List.length_cons] at he
      omega
end
end MISLocal


/- ===== Source: MISLocal/FiniteTreePermutations.lean ===== -/
/-! Finite involutions agreeing with the colored regular tree inside a word ball. -/
open scoped Classical
namespace MISLocal
noncomputable section
namespace FiniteTree
variable {α : Type*} [DecidableEq α]
def Reduced : List α → Prop
  | [] => True
  | [_] => True
  | i::j::w => i ≠ j ∧ Reduced (j::w)
omit [DecidableEq α] in
theorem reduced_tail {i : α} {w : List α} (h : Reduced (i::w)) : Reduced w := by
  cases w with
  | nil => trivial
  | cons j w => exact h.2
def rawToggle (i : α) : List α → List α
  | [] => [i]
  | j::w => if j = i then w else i::j::w
theorem rawToggle_reduced (i : α) {w : List α} (h : Reduced w) : Reduced (rawToggle i w) := by
  cases w with
  | nil => trivial
  | cons j w =>
    by_cases hj : j = i
    · simpa only [rawToggle,if_pos hj] using reduced_tail h
    · simpa only [rawToggle,if_neg hj,Reduced] using And.intro (Ne.symm hj) h
theorem rawToggle_involutive (i : α) {w : List α} (h : Reduced w) : rawToggle i (rawToggle i w) = w := by
  cases w with
  | nil => simp [rawToggle]
  | cons j w =>
    by_cases hj : j = i
    · subst j
      cases w with
      | nil => simp [rawToggle]
      | cons j w =>
        have hj : j ≠ i := Ne.symm h.1
        simp [rawToggle,hj]
    · simp [rawToggle,hj]
theorem rawToggle_length (i : α) (w : List α) : (rawToggle i w).length ≤ w.length+1 := by
  cases w <;> simp only [rawToggle,List.length_nil,List.length_cons]
  · omega
  · split
    · omega
    · simp only [List.length_cons]
      omega
def Word (α : Type*) (L : ℕ) := {w : List α // Reduced w ∧ w.length ≤ L}
instance [Finite α] (L : ℕ) : Finite (Word α L) :=
  Set.Finite.to_subtype ((List.finite_length_le α L).subset (fun _ h => h.2))
instance [Fintype α] (L : ℕ) : Fintype (Word α L) := Fintype.ofFinite _
def emptyWord (L : ℕ) : Word α L := ⟨[],by simp [Reduced]⟩
def toggle (L : ℕ) (i : α) (w : Word α L) : Word α L :=
  if h : (rawToggle i w.val).length ≤ L then
    ⟨rawToggle i w.val,rawToggle_reduced i w.property.1,h⟩ else w
theorem toggle_involutive (L : ℕ) (i : α) : Function.Involutive (toggle L i) := by
  intro w
  by_cases h : (rawToggle i w.val).length ≤ L
  · have he := rawToggle_involutive i w.property.1
    have hh : (rawToggle i (rawToggle i w.val)).length ≤ L := by rw [he]; exact w.property.2
    apply Subtype.ext
    simp only [toggle,dif_pos h,dif_pos hh]
    exact he
  · simp only [toggle,dif_neg h]
def generator (L : ℕ) (i : α) : Equiv.Perm (Word α L) :=
  ⟨toggle L i,toggle L i,toggle_involutive L i,toggle_involutive L i⟩
theorem generator_sq (L : ℕ) (i : α) : generator L i * generator L i = 1 := by
  ext w
  exact toggle_involutive L i w
theorem generator_val {L : ℕ} (i : α) (w : Word α L) (h : w.val.length < L) :
    (generator L i w).val = rawToggle i w.val := by
  have hb : (rawToggle i w.val).length ≤ L := le_trans (rawToggle_length i _) (by omega)
  simp only [generator,Equiv.coe_fn_mk,toggle,dif_pos hb]
theorem generator_empty {L : ℕ} (hL : 1 ≤ L) (i : α) :
    (generator L i (emptyWord L)).val = [i] :=
  generator_val i (emptyWord L) (by simpa only [emptyWord,List.length_nil] using hL)
def product (L : ℕ) : List α → Equiv.Perm (Word α L)
  | [] => 1
  | i::w => generator L i * product L w
theorem product_toggle (L : ℕ) (i : α) {w : List α} (h : Reduced w) :
    product L (rawToggle i w) = generator L i * product L w := by
  cases w with
  | nil => simp [rawToggle,product]
  | cons j w =>
    by_cases hj : j = i
    · subst j
      simp [rawToggle,product,← mul_assoc,generator_sq]
    · simp only [rawToggle,if_neg hj,product]
theorem product_eval (L : ℕ) {w : List α} (h : Reduced w) (hL : w.length ≤ L) :
    (product L w (emptyWord L)).val = w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hwL : w.length < L := by simpa only [List.length_cons] using hL
    have hw := ih (reduced_tail h) (Nat.le_of_lt hwL)
    change (generator L i (product L w (emptyWord L))).val = i::w
    rw [generator_val i _ (by rw [hw]; exact hwL),hw]
    cases w with
    | nil => rfl
    | cons j w => simp only [rawToggle,if_neg (Ne.symm h.1)]
theorem product_eval_injective (L : ℕ) : Function.Injective (fun w : Word α L => product L w.val) := by
  intro w z h
  have he := congrArg (fun p : Equiv.Perm (Word α L) => (p (emptyWord L)).val) h
  dsimp only at he
  rw [product_eval L w.property.1 w.property.2,product_eval L z.property.1 z.property.2] at he
  exact Subtype.ext he
end FiniteTree
end
end MISLocal


/- ===== Source: MISLocal/FiniteRegularSkeleton.lean ===== -/
/-! Finite D-regular skeletons with arbitrarily deep tree edge neighborhoods. -/
open scoped Classical
namespace MISLocal
noncomputable section
namespace FiniteTree
open TreeGeometry
variable {D L : ℕ}
abbrev Vertex (D L : ℕ) := Equiv.Perm (Word (Fin D) L)
theorem generator_ne_one (hL : 1 ≤ L) (i : Fin D) : generator L i ≠ 1 := by
  intro h
  have he := congrArg (fun p : Vertex D L => (p (emptyWord L)).val) h
  dsimp only at he
  rw [generator_empty hL i] at he
  simp [emptyWord] at he
theorem generator_injective (hL : 1 ≤ L) : Function.Injective (generator L (α := Fin D)) := by
  intro i j h
  have he := congrArg (fun p : Vertex D L => (p (emptyWord L)).val) h
  dsimp only at he
  simpa only [generator_empty hL,List.cons.injEq,and_true] using he
def graph (D L : ℕ) (hL : 1 ≤ L) : SimpleGraph (Vertex D L) where
  Adj p q := ∃ i : Fin D, q = generator L i * p
  symm := by
    rintro p q ⟨i,rfl⟩
    exact ⟨i,by simp only [← mul_assoc,generator_sq,one_mul]⟩
  loopless := by
    rintro p ⟨i,hi⟩
    have he : generator L i = 1 := mul_right_cancel (hi.symm.trans (one_mul p).symm)
    exact generator_ne_one hL i he
def neighborEquiv (hL : 1 ≤ L) (p : Vertex D L) : Fin D ≃ (graph D L hL).neighborSet p :=
  Equiv.ofBijective (fun i => ⟨generator L i*p,⟨i,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact generator_injective hL (mul_right_cancel (congrArg Subtype.val h))
    · rintro ⟨q,i,hq⟩
      exact ⟨i,Subtype.ext hq.symm⟩)
theorem graph_regular (hL : 1 ≤ L) (p : Vertex D L) : (graph D L hL).degree p = D := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (neighborEquiv hL p)).symm.trans (Fintype.card_fin D)
def evaluation (root p : Vertex D L) : List (Fin D) := ((p*root⁻¹) (emptyWord L)).val
theorem ball_representation (hL : 1 ≤ L) (root : Vertex D L) {t : ℕ} (ht : t ≤ L)
    (p : Vertex D L) (hb : InBall (graph D L hL) t p root) :
    (evaluation root p).length ≤ t ∧ p*root⁻¹ = product L (evaluation root p) := by
  induction t generalizing p with
  | zero => subst p; simp [evaluation,emptyWord,product]
  | succ t ih =>
    rcases hb with hp | ⟨q,hpq,hq⟩
    · subst p; simp [evaluation,emptyWord,product]
    · obtain ⟨hqL,hrep⟩ := ih (by omega) q hq
      obtain ⟨i,hpi⟩ := hpq.symm
      have heval : evaluation root p = rawToggle i (evaluation root q) := by
        change ((p*root⁻¹) (emptyWord L)).val = _
        rw [hpi,mul_assoc]
        exact generator_val i _ (by exact lt_of_le_of_lt hqL (by omega))
      constructor
      · rw [heval]; exact (rawToggle_length i _).trans (by omega)
      · have hred : Reduced (evaluation root q) := ((q*root⁻¹) (emptyWord L)).property.1
        rw [heval,product_toggle L i (w := evaluation root q) hred,← hrep,hpi]
        exact mul_assoc _ _ _
theorem ball_evaluation_injective (hL : 1 ≤ L) (root : Vertex D L) {t : ℕ} (ht : t ≤ L) :
    Set.InjOn (evaluation root) {p | InBall (graph D L hL) t root p} := by
  intro p hp q hq he
  have hpr := (ball_representation hL root ht p (inBall_symm _ t hp)).2
  have hqr := (ball_representation hL root ht q (inBall_symm _ t hq)).2
  exact mul_right_cancel (hpr.trans (he ▸ hqr.symm))
theorem rawToggle_adj (i : Fin D) (w : List (Fin D)) :
    (prefixTree (Fin D)).Adj w (rawToggle i w) := by
  cases w with
  | nil => exact Or.inr ⟨i,rfl⟩
  | cons j w =>
    by_cases hj : j = i
    · simp only [rawToggle,if_pos hj]; exact Or.inl ⟨j,rfl⟩
    · simp only [rawToggle,if_neg hj]; exact Or.inr ⟨i,rfl⟩
theorem evaluation_adj (hL : 1 ≤ L) (root : Vertex D L) {t : ℕ} (ht : t < L)
    {p q : Vertex D L} (hp : InBall (graph D L hL) t root p)
    (ha : (graph D L hL).Adj p q) :
    (prefixTree (Fin D)).Adj (evaluation root p) (evaluation root q) := by
  obtain ⟨i,rfl⟩ := ha
  have hpL := (ball_representation hL root (Nat.le_of_lt ht) p (inBall_symm _ t hp)).1
  have he : evaluation root (generator L i*p) = rawToggle i (evaluation root p) := by
    unfold evaluation
    rw [mul_assoc]
    exact generator_val i _ (hpL.trans_lt ht)
  rw [he]; exact rawToggle_adj i _
theorem edgeRegion_in_ball (hL : 1 ≤ L) (e : (graph D L hL).edgeSet) (t : ℕ) :
    edgeRegion (graph D L hL) e t ⊆ {p | InBall (graph D L hL) (t+1) (edgeLeft (graph D L hL) e) p} := by
  induction t with
  | zero =>
    intro p hp
    change p ∈ e.val at hp
    rw [← edge_endpoints (graph D L hL) e,Sym2.mem_iff] at hp
    rcases hp with hp | hp
    · subst p; exact inBall_self _ 1 _
    · subst p; exact Or.inr ⟨_,endpoint_adj _ e,rfl⟩
  | succ t ih =>
    rintro p (hp | ⟨q,hq,hpq⟩)
    · exact inBall_mono_succ _ _ _ _ (ih hp)
    · exact inBall_append _ (t+1) (ih hq) hpq.symm
theorem graph_edgeRegion_tree (hL : 1 ≤ L) {r : ℕ} (hr : r+1 < L)
    (e : (graph D L hL).edgeSet) : ((graph D L hL).induce (edgeRegion (graph D L hL) e r)).IsTree := by
  refine ⟨edgeRegion_connected _ e r,?_⟩
  let root := edgeLeft (graph D L hL) e
  let f : (graph D L hL).induce (edgeRegion (graph D L hL) e r) →g prefixTree (Fin D) :=
    ⟨fun p => evaluation root p.val,fun {p q} h =>
      evaluation_adj hL root hr (edgeRegion_in_ball hL e r p.property) h⟩
  have hf : Function.Injective f := by
    intro p q h
    exact Subtype.ext (ball_evaluation_injective hL root (Nat.le_of_lt hr)
      (edgeRegion_in_ball hL e r p.property) (edgeRegion_in_ball hL e r q.property) h)
  intro p w hw
  exact prefixTree_acyclic (Fin D) (w.map f) (hw.map hf)
end FiniteTree
end
end MISLocal


/- ===== Source: MISLocal/EmbeddedLocalExecution.lean ===== -/
/-! Transport local execution along an embedding with closed incident rows. -/
open scoped Classical
namespace MISLocal
noncomputable section
theorem inBall_hom {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y)
    (f : G →g H) (t : ℕ) {v w : X} (h : InBall G t v w) : InBall H t (f v) (f w) := by
  induction t generalizing v w with
  | zero => exact congrArg f h
  | succ t ih =>
    rcases h with h | ⟨u,hvu,huw⟩
    · exact Or.inl (congrArg f h)
    · exact Or.inr ⟨f u,f.map_adj hvu,ih huw⟩
namespace UniformLocalProtocol
variable {n : ℕ} {Tape State X Y B : Type*} [Fintype X] [Fintype Y]
theorem neighborImage_embedding [DecidableEq B] (G : SimpleGraph X) (H : SimpleGraph Y)
    (φ : X → Y) (v : X) (f : X → B) (g : Y → B)
    (hrow : ∀ u, G.Adj v u ↔ H.Adj (φ v) (φ u))
    (hclosed : ∀ u, H.Adj (φ v) u → ∃ w, φ w = u)
    (hdata : ∀ u, G.Adj v u → f u = g (φ u)) :
    (Finset.univ.filter (G.Adj v)).image f = (Finset.univ.filter (H.Adj (φ v))).image g := by
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,huz⟩ := Finset.mem_image.mp hz
    have ha := (Finset.mem_filter.mp hu).2
    exact Finset.mem_image.mpr ⟨φ u,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(hrow u).mp ha⟩,(hdata u ha).symm.trans huz⟩
  · intro hz
    obtain ⟨u,hu,huz⟩ := Finset.mem_image.mp hz
    have ha := (Finset.mem_filter.mp hu).2
    obtain ⟨w,rfl⟩ := hclosed u ha
    have haw := (hrow w).mpr ha
    exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,haw⟩,(hdata w haw).trans huz⟩
theorem run_embedding (A : UniformLocalProtocol n Tape State)
    (G : SimpleGraph X) (H : SimpleGraph Y) (φ : X → Y)
    (ids : X → Fin n) (ids' : Y → Fin n) (W : Fin n → Tape) (t : ℕ) (v : X)
    (hids : ∀ u, InBall G (t+1) v u → ids u = ids' (φ u))
    (hrows : ∀ u, InBall G t v u → ∀ w, G.Adj u w ↔ H.Adj (φ u) (φ w))
    (hclosed : ∀ u, InBall G t v u → ∀ w, H.Adj (φ u) w → ∃ z, φ z = w) :
    A.run G ids W t v = A.run H ids' W t (φ v) := by
  induction t generalizing v with
  | zero =>
    have hv := hids v (inBall_self G 1 v)
    have hn : neighbors G ids v = neighbors H ids' (φ v) :=
      neighborImage_embedding G H φ v ids ids' (hrows v rfl) (hclosed v rfl)
        (fun u hu => hids u (Or.inr ⟨u,hu,rfl⟩))
    simp only [run,hv,hn]
  | succ t ih =>
    have hv := hids v (inBall_self G (t+1+1) v)
    have hr := hrows v (inBall_self G (t+1) v)
    have hc := hclosed v (inBall_self G (t+1) v)
    have hs := ih v
      (fun u hu => hids u (inBall_mono_succ G (t+1) v u hu))
      (fun u hu => hrows u (inBall_mono_succ G t v u hu))
      (fun u hu => hclosed u (inBall_mono_succ G t v u hu))
    have hn : (Finset.univ.filter (G.Adj v)).image (fun u => (ids u,A.run G ids W t u)) =
        (Finset.univ.filter (H.Adj (φ v))).image (fun u => (ids' u,A.run H ids' W t u)) := by
      apply neighborImage_embedding G H φ v _ _ hr hc
      intro u hu
      refine Prod.ext (hids u (Or.inr ⟨u,hu,inBall_self G (t+1) u⟩)) ?_
      exact ih u (fun w hw => hids w (Or.inr ⟨u,hu,hw⟩))
        (fun w hw => hrows w (Or.inr ⟨u,hu,hw⟩)) (fun w hw => hclosed w (Or.inr ⟨u,hu,hw⟩))
    simp only [run,hv,hs,hn]
theorem run_induce (A : UniformLocalProtocol n Tape State) (G : SimpleGraph X)
    (U : Set X) (ids : X → Fin n) (W : Fin n → Tape) (t : ℕ) (v : U)
    (hball : ∀ w, InBall G (t+1) v.val w → w ∈ U) :
    A.run (G.induce U) (fun w => ids w.val) W t v = A.run G ids W t v.val := by
  apply A.run_embedding (G.induce U) G Subtype.val _ _ W t v
  · exact fun _ _ => rfl
  · exact fun _ _ _ => Iff.rfl
  · intro u hu w huw
    let inclusion : (G.induce U) →g G := ⟨Subtype.val,fun h => h⟩
    have hb : InBall G t v.val u.val := inBall_hom _ _ inclusion t hu
    exact ⟨⟨w,hball w (inBall_append G t hb huw)⟩,rfl⟩
end UniformLocalProtocol
end
end MISLocal


/- ===== Source: MISLocal/LocalGraphRealization.lean ===== -/
/-! Realize a local neighborhood on exactly n legal identifiers, padding with isolated vertices. -/
open scoped Classical
namespace MISLocal
noncomputable section
def localIDEmbedding {X : Type*} [Fintype X] {n : ℕ} (U : Set X)
    (ids : X → Fin n) (hn : Fintype.card U ≤ n) : U ↪ Fin n :=
  if h : Set.InjOn ids U then
    ⟨fun u => ids u.val,fun u v huv => Subtype.ext (h u.property v.property huv)⟩
  else Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hn))
theorem localIDEmbedding_agrees {X : Type*} [Fintype X] {n : ℕ} (U : Set X)
    (ids : X → Fin n) (hn : Fintype.card U ≤ n) (hi : Set.InjOn ids U) (u : U) :
    localIDEmbedding U ids hn u = ids u.val := by
  simp only [localIDEmbedding,dif_pos hi,Function.Embedding.coeFn_mk]
def localRealization {X : Type*} [Fintype X] {n : ℕ} (H : SimpleGraph X)
    (U : Set X) (ids : X → Fin n) (hn : Fintype.card U ≤ n) : SimpleGraph (Fin n) :=
  (H.induce U).map (localIDEmbedding U ids hn)
namespace UniformLocalProtocol
variable {n : ℕ} {Tape State X : Type*} [Fintype X]
theorem run_map (A : UniformLocalProtocol n Tape State) (G : SimpleGraph X)
    (φ : X ↪ Fin n) (ids : X → Fin n) (W : Fin n → Tape) (t : ℕ) (v : X)
    (hi : ∀ u, ids u = φ u) : A.run G ids W t v = A.run (G.map φ) id W t (φ v) := by
  apply A.run_embedding G (G.map φ) φ ids id W t v
  · exact fun u _ => hi u
  · exact fun _ _ _ => SimpleGraph.map_adj_apply.symm
  · intro u _ w hw
    obtain ⟨a,b,_,_,hb⟩ := hw
    exact ⟨b,hb⟩
theorem candidates_realization (A : UniformLocalProtocol n Tape State)
    (H : SimpleGraph X) (U : Set X) (ids : X → Fin n) (hn : Fintype.card U ≤ n)
    (W : Fin n → Tape) (t : ℕ) (z : U) (hi : Set.InjOn ids U)
    (hball : ∀ w, InBall H (t+1) z.val w → w ∈ U) :
    z.val ∈ A.candidates H ids W t ↔ localIDEmbedding U ids hn z ∈
      A.candidates (localRealization H U ids hn) id W t := by
  have he := (A.run_induce H U ids W t z hball).symm.trans
    (A.run_map (H.induce U) (localIDEmbedding U ids hn) (fun u => ids u.val)
      W t z (localIDEmbedding_agrees U ids hn hi · |>.symm))
  simp only [candidates,Set.mem_setOf_eq,localRealization,localIDEmbedding_agrees U ids hn hi,he,id_eq]
end UniformLocalProtocol
theorem realization_forces_repaired_occupancy {n : ℕ} {Tape State X : Type*} [Fintype X]
    (A : UniformLocalProtocol n Tape State) (H : SimpleGraph X) (C U : Set X)
    (ids : X → Fin n) (hn : Fintype.card U ≤ n) (W : Fin n → Tape) (T : ℕ)
    (candidates : Set X) (hi : Set.InjOn ids U) (hno : ¬ExternallyDominatable H C)
    (hlocal : ∀ v ∈ C, ∀ z, z = v ∨ H.Adj v z → z ∈ U ∧
      (∀ w, InBall H (T+1) z w → w ∈ U) ∧ (z ∈ candidates ↔ z ∈ A.candidates H ids W T))
    (hcorrect : Maximal (localRealization H U ids hn).IsIndepSet
      (A.candidates (localRealization H U ids hn) id W T)) : Occupies C (repair H candidates) := by
  let φ := localIDEmbedding U ids hn
  let K := localRealization H U ids hn
  let out := A.candidates K id W T
  let S : Set X := {x | ∃ u : U, u.val = x ∧ φ u ∈ out}
  have hind : H.IsIndepSet S := by
    rintro x ⟨u,rfl,hu⟩ y ⟨v,rfl,hv⟩ hxy hAdj
    have ha : K.Adj (φ u) (φ v) := ⟨u,v,hAdj,rfl,rfl⟩
    exact hcorrect.1 hu hv ha.ne ha
  have hsim : ∀ v ∈ C, ∀ z, z = v ∨ H.Adj v z → (z ∈ candidates ↔ z ∈ S) := by
    intro v hv z hz
    obtain ⟨hzu,hball,hcand⟩ := hlocal v hv z hz
    let zu : U := ⟨z,hzu⟩
    have hrun := A.candidates_realization H U ids hn W T zu hi hball
    constructor
    · intro hs; exact ⟨zu,rfl,hrun.mp (hcand.mp hs)⟩
    · rintro ⟨u,hu,hs⟩
      have he : u = zu := Subtype.ext hu
      subst u
      exact hcand.mpr (hrun.mpr hs)
  have hoc : Occupies C S := by
    by_contra hnocc
    apply hno
    refine ⟨S,hind,Set.disjoint_left.mpr (fun x hx hs => hnocc ⟨x,hx,hs⟩),?_⟩
    intro v hv
    have hvu := (hlocal v hv v (Or.inl rfl)).1
    let vu : U := ⟨v,hvu⟩
    have hvnot : φ vu ∉ out := fun hs => hnocc ⟨v,hv,vu,rfl,hs⟩
    obtain ⟨w,hw,hvw⟩ := maximal_independent_dominates K hcorrect hvnot
    obtain ⟨a,b,hab,ha,hb⟩ := hvw
    have hav : a = vu := φ.injective ha
    subst a
    exact ⟨b.val,⟨b,rfl,hb ▸ hw⟩,hab⟩
  exact (repair_occupancy_agrees H hind hsim).mpr hoc
end
end MISLocal


/- ===== Source: MISLocal/SuccessObstruction.lean ===== -/
/-! Averaging only needs success on a legal realization to force repaired occupancy. -/
open MeasureTheory
namespace MISLocal
noncomputable section
theorem success_obstruction {Ω W : Type*} [Fintype Ω] [MeasurableSpace W]
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (unique bad : Ω → Prop) (success occupied : Ω → W → Prop)
    (ε δ γ β : ℝ) (hε : ε ≤ 1)
    (hcollision : μ.prob (fun g => ¬unique g) ≤ δ) (hbad : μ.prob bad ≤ γ)
    (hcorrect : ∀ g, 1-ε ≤ ν.real {w | success g w})
    (hforce : ∀ g, unique g → ¬bad g → ∀ w, success g w → occupied g w)
    (hmeas : ∀ g, MeasurableSet {w | occupied g w})
    (hfixed : ∀ w, μ.prob (fun g => occupied g w) ≤ β) : (1-ε)*(1-δ-γ) ≤ β := by
  classical
  let good := fun g => unique g ∧ ¬bad g
  have hlower : 1-δ-γ ≤ μ.prob good := by
    have hi := μ.prob_and_lower unique (fun g => ¬bad g)
    rw [μ.prob_not] at hi
    have hu := μ.prob_not unique
    dsimp only [good]
    linarith
  have hpoint : ∀ g, (1-ε)*bit (good g) ≤ ν.real {w | occupied g w} := by
    intro g
    by_cases hg : good g
    · have hs : {w | success g w} ⊆ {w | occupied g w} := hforce g hg.1 hg.2
      simpa [bit,hg] using (hcorrect g).trans (measureReal_mono hs)
    · simp [bit,hg,measureReal_nonneg]
  have hmean := μ.expect_mono hpoint
  rw [μ.expect_mul] at hmean
  have hupper := average_fixed_tape_bound μ ν (fun g => {w | occupied g w}) hmeas β hfixed
  exact (mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hε)).trans (hmean.trans hupper)
end
end MISLocal


/- ===== Source: MISLocal/LocalSizeObstruction.lean ===== -/
/-! Only the local clique ball needs to fit on the n-vertex legal input. -/
open MeasureTheory
open scoped Classical
namespace MISLocal
noncomputable section
namespace TreeGeometry
variable {V Tape State : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m b : ℕ}
    (pack : (Fin (2*m) × Fin b) ↪ (Fin m × Fin m))
    (A : UniformLocalProtocol (2^b) Tape State) [MeasurableSpace Tape]
    (ν : Measure (Fin (2^b) → Tape)) [IsProbabilityMeasure ν] (T : ℕ)
theorem local_size_obstruction {d : ℕ} (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (T+3))).IsTree) (e : G.edgeSet)
    (hfit : (ballFinset G (T+2) (edgeLeft G e)).card*(2*m) ≤ 2^b)
    (ε : ℝ) (hε : ε ≤ 1)
    (hcorrect : ∀ K : SimpleGraph (Fin (2^b)), 1-ε ≤ ν.real {W | Maximal K.IsIndepSet (A.candidates K id W T)})
    (hmeas : ∀ (M : G.edgeSet → EdgeMatrix (2*m)) (z : V × Fin (2*m)),
      MeasurableSet {W | z ∈ A.candidates (cliqueBlowup G M) (extractedIdentifiers G pack M) W T})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ 2*m)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log ((2*m:ℕ):ℝ))
    (hupper : Real.log ((2*m:ℕ):ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (1-ε)*(1-localCollisionError G (m := m) (b := b) T (edgeLeft G e)-
      localDominationError (m := m) (d+1)) ≤ occupancyCap (T+3) ((d+1:ℕ):ℝ) := by
  let μ := FiniteProb.pi (matrixPrivateProbability G (2*m) (fun _ => FiniteProb.uniform Unit))
  let matrix := fun ω : ∀ i, matrixPrivateType G (2*m) (fun _ => Unit) i => fun e => ω (Sum.inl e)
  let root := edgeLeft G e
  let H := fun ω => cliqueBlowup G (matrix ω)
  let U : Set (V × Fin (2*m)) := {z | InBall G (T+2) root z.1}
  have hn : Fintype.card U ≤ 2^b := by
    calc
      Fintype.card U = Fintype.card {z : V × Fin (2*m) // InBall G (T+2) root z.1} := Fintype.card_congr (Equiv.refl _)
      _ = (ballFinset G (T+2) root).card*(2*m) := cliqueBall_card G root
      _ ≤ 2^b := hfit
  let ids := fun ω => extractedIdentifiers G pack (matrix ω)
  let K := fun ω => localRealization (H ω) U (ids ω) hn
  let S := fun ω W => snapshotCandidates pack A W T (fullEdgeSnapshot G (matrix ω) root)
  let unique := fun ω => locallyUniqueIDs G pack T root (matrix ω)
  apply success_obstruction μ ν unique (fun ω => ExternallyDominatable (H ω) (vertexClique root))
    (fun ω W => Maximal (K ω).IsIndepSet (A.candidates (K ω) id W T))
    (fun ω W => Occupies (vertexClique root) (repair (H ω) (S ω W))) ε
    (localCollisionError G (m := m) (b := b) T root) (localDominationError (m := m) (d+1)) _ hε
  · dsimp only [μ,unique,locallyUniqueIDs,matrix]
    rw [matrixUnitProbability_prob G (2*m)
      (fun M => ¬Set.InjOn (extractedIdentifiers G pack M) {z | InBall G (T+2) root z.1})]
    exact extracted_local_collision_bound G pack (by intro v; rw [hreg]; omega) (T+2) root
  · dsimp only [μ,H,matrix]
    rw [matrixUnitProbability_prob G (2*m) (fun M => ExternallyDominatable (cliqueBlowup G M) (vertexClique root))]
    have h := external_domination_probability G (k := 2*m) root
    rw [hreg root] at h
    exact h
  · exact fun ω => hcorrect (K ω)
  · intro ω hu hno W hc
    apply realization_forces_repaired_occupancy A (H ω) (vertexClique root) U (ids ω) hn W T (S ω W) hu hno _ hc
    intro v hv z hz
    have hvr : v.1 = root := hv
    have hzr : InBall G 1 root z.1 := by
      rcases hz with hz | hz
      · exact Or.inl ((congrArg Prod.fst hz).trans hvr)
      · rcases blowup_adj_skeleton G (matrix ω) hz with he | ha
        · exact Or.inl (he.symm.trans hvr)
        · exact Or.inr ⟨z.1,hvr ▸ ha,rfl⟩
    have hball (w : V × Fin (2*m)) (hw : InBall G (T+1) z.1 w.1) : w ∈ U := by
      simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using inBall_trans G hzr hw
    have hzu : z ∈ U := hball z (inBall_self G (T+1) z.1)
    refine ⟨hzu,fun w hw => hball w (blowup_ball_skeleton G (matrix ω) (T+1) z w hw),?_⟩
    have huniq : snapshotUnique pack T (fullEdgeSnapshot G (matrix ω) root) z.1 := by
      unfold snapshotUnique
      rw [fullSnapshotIdentifiers G pack (matrix ω) root,fullSnapshotSkeleton G (matrix ω) root]
      exact fun a ha b hb hab => hu (hball a ha) (hball b hb) hab
    simp only [S,snapshotCandidates,Set.mem_setOf_eq,huniq,true_and,
      fullSnapshotBlowup G (matrix ω) root,fullSnapshotIdentifiers G pack (matrix ω) root]
    rfl
  · intro ω
    apply repaired_occupancy_measurable (H ω) (vertexClique root) (S ω)
    intro z
    by_cases hu : snapshotUnique pack T (fullEdgeSnapshot G (matrix ω) root) z.1
    · have h := hmeas (matrix ω) z
      simpa only [S,snapshotCandidates,Set.mem_setOf_eq,hu,true_and,
        fullSnapshotBlowup G (matrix ω) root,fullSnapshotIdentifiers G pack (matrix ω) root] using h
    · simp only [S,snapshotCandidates,Set.mem_setOf_eq,hu,false_and]; exact MeasurableSet.empty
  · exact fun W => concrete_fixed_table_occupancy G pack A W T hreg ht e hD hk hlower hupper
end TreeGeometry
end
end MISLocal


/- ===== Source: MISLocal/PowerSizeParameters.lean ===== -/
/-! Explicit finite powers-of-two size, matrix-capacity and probability estimates. -/
open scoped Classical
namespace MISLocal
noncomputable section
namespace PowerSize
def degree (s : ℕ) := 2^s
def halfClique (D : ℕ) := 2^(2*D)
def bits (D : ℕ) := 6*D+1
def size (s : ℕ) := 2^(bits (degree s))
theorem log_two_bounds : (1/2:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h
    exact h
  · have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h
    exact h
theorem cube_le_two_pow {D : ℕ} (hD : 10 ≤ D) : D^3 ≤ 2^D := by
  induction D,hD using Nat.le_induction with
  | base => norm_num
  | succ D hD ih =>
    rw [pow_succ (2:ℕ) D]
    have h1 : 10*D ≤ D^2 := by nlinarith [Nat.mul_le_mul_left D hD]
    have h2 : 10*D^2 ≤ D^3 := by nlinarith [Nat.mul_le_mul_left (D*D) hD]
    have hc : (D+1)^3 ≤ 2*D^3 := by nlinarith
    exact hc.trans (by nlinarith)
theorem clique_power (D : ℕ) : 2*halfClique D = 2^(2*D+1) := by
  simp only [halfClique,pow_succ]
  omega
theorem packing_exists {D : ℕ} (hD : 10 ≤ D) :
    Nonempty ((Fin (2*halfClique D) × Fin (bits D)) ↪ (Fin (halfClique D) × Fin (halfClique D))) := by
  apply Function.Embedding.nonempty_of_card_le
  simp only [Fintype.card_prod,Fintype.card_fin]
  have he : D^3 ≤ halfClique D := (cube_le_two_pow hD).trans
    (pow_le_pow_right' (by omega : 1 ≤ (2:ℕ)) (by omega))
  have hm : 2*bits D ≤ halfClique D := by
    have h1 : 10*D ≤ D^2 := by nlinarith [Nat.mul_le_mul_left D hD]
    have h2 : 10*D^2 ≤ D^3 := by nlinarith [Nat.mul_le_mul_left (D*D) hD]
    unfold bits
    nlinarith
  nlinarith
theorem clique_log_bounds {D : ℕ} (hD : 10 ≤ D) :
    (D:ℝ) ≤ Real.log ((2*halfClique D:ℕ):ℝ) ∧
      Real.log ((2*halfClique D:ℕ):ℝ) ≤ (D:ℝ)^2 := by
  rw [clique_power,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  push_cast
  have hd : (10:ℝ) ≤ D := by exact_mod_cast hD
  have hlog := log_two_bounds
  constructor <;> nlinarith
theorem domination_error_small {D : ℕ} (hD : 10 ≤ D) :
    TreeGeometry.localDominationError (m := halfClique D) D ≤ (1/8:ℝ) := by
  let k : ℝ := ((2*halfClique D:ℕ):ℝ)
  have hk : k = (2:ℝ)^(2*D+1) := by
    dsimp only [k]
    rw [clique_power,Nat.cast_pow,Nat.cast_ofNat]
  have hk1 : k+1 ≤ (2:ℝ)^(2*D+2) := by
    rw [hk,show 2*D+2 = (2*D+1)+1 by omega,pow_succ (2:ℝ) (2*D+1)]
    have hone : (1:ℝ) ≤ 2^(2*D+1) := one_le_pow₀ (by norm_num)
    linarith
  have hlog : Real.log (k+1) ≤ (2*(D:ℝ)+2) := by
    have hh := Real.log_le_log (show 0<k+1 by dsimp [k]; positivity) hk1
    rw [Real.log_pow] at hh
    push_cast at hh
    have h2 := log_two_bounds.2
    nlinarith
  have hcancel : k*(2:ℝ)^(-(D:ℤ)) = 2*(2:ℝ)^D := by
    rw [hk,zpow_neg,zpow_natCast,show 2*D+1 = D+D+1 by omega,pow_succ,pow_add]
    have hp : (2:ℝ)^D ≠ 0 := by positivity
    field_simp
    ring
  have hcube : (D:ℝ)^3 ≤ (2:ℝ)^D := by exact_mod_cast cube_le_two_pow hD
  have hd : (10:ℝ) ≤ D := by exact_mod_cast hD
  have hexponent : (D:ℝ)*Real.log (k+1)-k*(2:ℝ)^(-(D:ℤ)) ≤ -(D:ℝ) := by
    rw [hcancel]
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg D)
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg (D:ℝ))]
  have hlog8 : Real.log (8:ℝ) ≤ 3 := by
    have he : Real.log (8:ℝ) = 3*Real.log 2 := by
      rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
      norm_num
    rw [he]
    nlinarith [log_two_bounds.2]
  have hexp : Real.exp (-(D:ℝ)) ≤ (1/8:ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 8) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<8)]; norm_num
  have heq : TreeGeometry.localDominationError (m := halfClique D) D =
      Real.exp ((D:ℝ)*Real.log (k+1)-k*(2:ℝ)^(-(D:ℤ))) := by
    unfold TreeGeometry.localDominationError
    simp only [Nat.cast_add,Nat.cast_one]
    change (k+1)^D*Real.exp (-k*(2:ℝ)^(-(D:ℤ))) = _
    rw [neg_mul,Real.exp_neg,Real.exp_sub,Real.exp_nat_mul (Real.log (k+1)) D,
      Real.exp_log (show 0<k+1 by dsimp [k]; positivity)]
    ring
  rw [heq]
  exact (Real.exp_le_exp.mpr hexponent).trans hexp
end PowerSize
end
end MISLocal


/- ===== Source: MISLocal/PowerBallEstimates.lean ===== -/
/-! Ball capacity and the collision error for the explicit parameter sequence. -/
open scoped Classical
namespace MISLocal
noncomputable section
namespace PowerSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s T : ℕ} (hreg : ∀ v, G.degree v ≤ degree s)

include hreg in
theorem ball_square_fit (root : V)
    (hsmall : 20000*(T+3)*(s+1) ≤ degree s) :
    8*((ballFinset G (T+2) root).card*(2*halfClique (degree s)))^2 ≤ size s := by
  let D := degree s
  let E := (s+1)*(T+2)+(2*D+1)
  have hD : 1 ≤ D := Nat.one_le_pow _ _ (by norm_num)
  have hb := ballFinset_card_le G hreg (T+2) root
  have hplus : D+1 ≤ 2^(s+1) := by
    change 2^s+1 ≤ 2^(s+1)
    rw [pow_succ]
    change 1 ≤ 2^s at hD
    omega
  have hL : (ballFinset G (T+2) root).card*(2*halfClique D) ≤ 2^E := by
    calc
      _ ≤ (D+1)^(T+2)*(2*halfClique D) := Nat.mul_le_mul_right _ hb
      _ ≤ (2^(s+1))^(T+2)*(2*halfClique D) :=
        Nat.mul_le_mul_right _ (pow_le_pow_left' hplus (T+2))
      _ = 2^E := by rw [clique_power,← pow_mul,← pow_add]
  have he : 2*E+3 ≤ bits D := by
    have hs : 20000*((s+1)*(T+3)) ≤ D := by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hsmall
    have hmin : 3 ≤ (s+1)*(T+3) := by nlinarith
    have hmon : (s+1)*(T+2) ≤ (s+1)*(T+3) := Nat.mul_le_mul_left _ (by omega)
    dsimp only [E,bits]
    nlinarith
  calc
    _ ≤ 8*(2^E)^2 := Nat.mul_le_mul_left _ (pow_le_pow_left' hL 2)
    _ = 2^(2*E+3) := by rw [← pow_mul,Nat.mul_comm E 2,pow_add]; norm_num; ring
    _ ≤ 2^(bits D) := pow_le_pow_right' (by norm_num) he

include hreg in
theorem ball_fits (root : V) (hsmall : 20000*(T+3)*(s+1) ≤ degree s) :
    (ballFinset G (T+2) root).card*(2*halfClique (degree s)) ≤ size s := by
  have h := ball_square_fit G hreg root hsmall
  have hl : ∀ L : ℕ, L ≤ 8*L^2 := by intro L; nlinarith
  exact (hl _).trans h

include hreg in
theorem collision_error_small (root : V) (hsmall : 20000*(T+3)*(s+1) ≤ degree s) :
    TreeGeometry.localCollisionError G (m := halfClique (degree s)) (b := bits (degree s)) T root ≤ (1/8:ℝ) := by
  let L := (ballFinset G (T+2) root).card*(2*halfClique (degree s))
  have hnat := ball_square_fit G hreg root hsmall
  have h : (8:ℝ)*(L:ℝ)^2 ≤ (size s:ℝ) := by exact_mod_cast hnat
  have hn : (0:ℝ) < size s := by dsimp only [size]; positivity
  change (L:ℝ)*((L:ℝ)-1)/(size s:ℝ) ≤ _
  apply (div_le_iff₀ hn).mpr
  have hL : (0:ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith

theorem small_occupancy_cap {s T : ℕ} (hsmall : 20000*(T+3)*(s+1) ≤ degree s) :
    occupancyCap (T+3) (degree s:ℝ) ≤ (1/4:ℝ) := by
  have hd : (0:ℝ) < degree s := by dsimp only [degree]; positivity
  have hs : (20000:ℝ)*((T:ℝ)+3)*((s:ℝ)+1) ≤ (degree s:ℝ) := by exact_mod_cast hsmall
  have he : Real.log (degree s:ℝ) = (s:ℝ)*Real.log 2 := by
    simp only [degree,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  unfold occupancyCap
  apply (min_le_right _ _).trans
  apply (div_le_iff₀ hd).mpr
  rw [he]
  push_cast
  have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hS : (0:ℝ) ≤ s := Nat.cast_nonneg _
  have hlog := mul_le_mul_of_nonneg_left log_two_bounds.2
    (show 0 ≤ 5000*((T:ℝ)+3)*(s:ℝ) by positivity)
  nlinarith
end PowerSize
end
end MISLocal


/- ===== Source: MISLocal/FiniteLocalLowerBound.lean ===== -/

/-! A finite LOCAL lower bound with every geometric, probability and parameter
premise discharged. Program measurability and MIS correctness are the only
algorithmic assumptions. No skeleton-existence or reduction hypothesis remains. -/

open MeasureTheory
open scoped Classical
namespace MISLocal
noncomputable section

/-- Ordinary measurability of the program's output as a function of its tapes.
This condition asserts no success, independence, symmetry or lower bound. -/
def MeasurableProgram {n : ℕ} {Tape State : Type} [MeasurableSpace Tape]
    (A : UniformLocalProtocol n Tape State) (T : ℕ) : Prop :=
  ∀ (X : Type) [Fintype X] (G : SimpleGraph X) (ids : X → Fin n) (v : X),
    MeasurableSet {W : Fin n → Tape | v ∈ A.candidates G ids W T}

namespace PowerSize
open TreeGeometry
theorem finite_local_round_bound {Tape State : Type} [MeasurableSpace Tape]
    (s T : ℕ) (hs : 20 ≤ s) (A : UniformLocalProtocol (size s) Tape State)
    (ν : Measure (Fin (size s) → Tape)) [IsProbabilityMeasure ν]
    (hmeas : MeasurableProgram A T)
    (hcorrect : ∀ K : SimpleGraph (Fin (size s)),
      (2/3:ℝ) ≤ ν.real {W | Maximal K.IsIndepSet (A.candidates K id W T)}) :
    degree s < 20000*(T+3)*(s+1) := by
  by_contra hfail
  have hsmall : 20000*(T+3)*(s+1) ≤ degree s := Nat.le_of_not_gt hfail
  have hD : 1048576 ≤ degree s := by
    have hp : (2:ℕ)^20 ≤ 2^s := pow_le_pow_right' (by norm_num) hs
    norm_num at hp
    exact hp
  have hd10 : 10 ≤ degree s := by omega
  let L := T+5
  have hL : 1 ≤ L := by omega
  let G := FiniteTree.graph (degree s) L hL
  letI : Nonempty (FiniteTree.Vertex (degree s) L) := ⟨1⟩
  have hreg : ∀ v, G.degree v = degree s := FiniteTree.graph_regular hL
  have hregle : ∀ v, G.degree v ≤ degree s := fun v => (hreg v).le
  have ht : ∀ e : G.edgeSet, (G.induce (TreeGeometry.edgeRegion G e (T+3))).IsTree :=
    FiniteTree.graph_edgeRegion_tree hL (by omega)
  let color : Fin (degree s) := ⟨0,by omega⟩
  let e : G.edgeSet := ⟨s(1,FiniteTree.generator L color),⟨color,by simp⟩⟩
  obtain ⟨pack⟩ := packing_exists hd10
  have hk : 1 ≤ 2*halfClique (degree s) := by
    have hp : 1 ≤ halfClique (degree s) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hd : degree s-1+1 = degree s := Nat.sub_add_cancel (by omega)
  have hlog := clique_log_bounds hd10
  have ho := TreeGeometry.local_size_obstruction G pack A ν T (d := degree s-1)
    (by intro v; rw [hd]; exact hreg v) ht e
    (ball_fits G hregle (TreeGeometry.edgeLeft G e) hsmall) (1/3) (by norm_num)
    (by intro K; convert hcorrect K using 1; norm_num)
    (fun M z => hmeas _ (cliqueBlowup G M) (extractedIdentifiers G pack M) z)
    (by simpa only [hd] using hD) hk
    (by simpa only [hd] using hlog.1) (by simpa only [hd] using hlog.2)
  rw [hd] at ho
  have hδ := collision_error_small G hregle (TreeGeometry.edgeLeft G e) hsmall
  have hγ := domination_error_small hd10
  have hhalf := obstruction_at_least_half (ε := (1/3:ℝ)) (by norm_num) (by linarith :
    TreeGeometry.localCollisionError G (m := halfClique (degree s)) (b := bits (degree s)) T
      (TreeGeometry.edgeLeft G e) + TreeGeometry.localDominationError (m := halfClique (degree s))
      (degree s) ≤ 1/4)
  have hcap := small_occupancy_cap hsmall
  linarith
end PowerSize
end
end MISLocal


/- ===== Source: MISLocal/AsymptoticLocalLowerBound.lean ===== -/

/-! The asymptotic randomized LOCAL MIS lower bound. The program, its state
space and tape distribution may depend on n. Correctness on every n-vertex
graph is required with probability at least 2/3. -/

open MeasureTheory Filter Asymptotics
open scoped Classical Topology
namespace MISLocal
noncomputable section

def localScale (n : ℕ) : ℝ := Real.log (n:ℝ)/Real.log (Real.log (n:ℝ))

namespace PowerSize
theorem size_gt_index (s : ℕ) : s < size s := by
  have h1 : s < degree s := Nat.lt_two_pow_self
  have h2 : degree s ≤ bits (degree s) := by unfold bits; omega
  have h3 : bits (degree s) < size s := Nat.lt_two_pow_self
  omega

theorem size_tendsto : Tendsto size atTop atTop := by
  apply tendsto_atTop.2
  intro n
  exact eventually_atTop.2 ⟨n,fun s hs => hs.trans (size_gt_index s).le⟩

theorem scale_upper {s : ℕ} (hs : 1 ≤ s) :
    0 ≤ localScale (size s) ∧ localScale (size s) ≤ 28*(degree s:ℝ)/((s:ℝ)+1) := by
  have hd : (0:ℝ) < degree s := by unfold degree; positivity
  have hsreal : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hln : (degree s:ℝ) ≤ Real.log (size s:ℝ) ∧
      Real.log (size s:ℝ) ≤ 7*(degree s:ℝ) := by
    rw [size,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    simp only [bits,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    have hd1 : (1:ℝ) ≤ degree s := by exact_mod_cast Nat.one_le_pow s (2:ℕ) (by norm_num)
    constructor <;> nlinarith [log_two_bounds.1,log_two_bounds.2]
  have hll : ((s:ℝ)+1)/4 ≤ Real.log (Real.log (size s:ℝ)) := by
    have hm := Real.log_le_log hd hln.1
    have he : Real.log (degree s:ℝ) = (s:ℝ)*Real.log 2 := by
      simp only [degree,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    rw [he] at hm
    have hh := mul_le_mul_of_nonneg_left log_two_bounds.1 (Nat.cast_nonneg s)
    nlinarith
  have hden : (0:ℝ) < ((s:ℝ)+1)/4 := by positivity
  have hllpos : 0 < Real.log (Real.log (size s:ℝ)) := hden.trans_le hll
  constructor
  · exact div_nonneg (hd.le.trans hln.1) hllpos.le
  · calc
      _ ≤ Real.log (size s:ℝ)/(((s:ℝ)+1)/4) := div_le_div_of_nonneg_left
        (hd.le.trans hln.1) hden hll
      _ ≤ (7*(degree s:ℝ))/(((s:ℝ)+1)/4) := div_le_div_of_nonneg_right hln.2 hden.le
      _ = _ := by field_simp; ring

theorem additive_slack {s : ℕ} (hs : 1000 ≤ s) : 240000*(s+1) ≤ degree s := by
  have hcube := cube_le_two_pow (by omega : 10 ≤ s)
  have h1 : 1000*s ≤ s^2 := by nlinarith [Nat.mul_le_mul_left s hs]
  have h2 : 1000*s^2 ≤ s^3 := by nlinarith [Nat.mul_le_mul_left (s*s) hs]
  exact le_trans (by nlinarith) hcube
end PowerSize

/-- No measurable uniform randomized LOCAL MIS algorithm family has
o(log n / log log n) worst-case rounds. The proof is valid for arbitrary
probability distributions on the tape tables, including independent infinite tapes. -/
theorem randomized_LOCAL_MIS_not_littleO
    (Tape State : ℕ → Type) [∀ n, MeasurableSpace (Tape n)]
    (rounds : ℕ → ℕ) (A : ∀ n, UniformLocalProtocol n (Tape n) (State n))
    (ν : ∀ n, Measure (Fin n → Tape n)) [∀ n, IsProbabilityMeasure (ν n)]
    (hmeas : ∀ n, MeasurableProgram (A n) (rounds n))
    (hcorrect : ∀ n (G : SimpleGraph (Fin n)),
      (2/3:ℝ) ≤ (ν n).real {W | Maximal G.IsIndepSet ((A n).candidates G id W (rounds n))}) :
    ¬IsLittleO atTop (fun n => (rounds n:ℝ)) localScale := by
  intro ho
  have hseq := ho.comp_tendsto PowerSize.size_tendsto
  have hbound := isLittleO_iff.mp hseq (c := (1/2240000:ℝ)) (by norm_num)
  obtain ⟨s,hb,hs⟩ := (hbound.and (eventually_ge_atTop (1000:ℕ))).exists
  have hscale := PowerSize.scale_upper (by omega : 1 ≤ s)
  have hb' : (rounds (PowerSize.size s):ℝ) ≤
      (1/2240000:ℝ)*localScale (PowerSize.size s) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,
      abs_of_nonneg (show (0:ℝ)≤(rounds (PowerSize.size s):ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg hscale.1] using hb
  have hround : (rounds (PowerSize.size s):ℝ) ≤
      (PowerSize.degree s:ℝ)/(80000*((s:ℝ)+1)) := by
    have hu := hb'.trans (mul_le_mul_of_nonneg_left hscale.2 (by norm_num : (0:ℝ)≤1/2240000))
    have he : (PowerSize.degree s:ℝ)/(80000*((s:ℝ)+1)) =
        (1/2240000:ℝ)*(28*(PowerSize.degree s:ℝ)/((s:ℝ)+1)) := by field_simp; ring
    rw [he]
    exact hu
  have hm := (le_div_iff₀ (show (0:ℝ)<80000*((s:ℝ)+1) by positivity)).mp hround
  have ha : (240000:ℝ)*((s:ℝ)+1) ≤ (PowerSize.degree s:ℝ) :=
    by exact_mod_cast PowerSize.additive_slack hs
  have hsmallreal : (20000:ℝ)*((rounds (PowerSize.size s):ℝ)+3)*((s:ℝ)+1) ≤ (PowerSize.degree s:ℝ) := by
    nlinarith
  have hsmall : 20000*(rounds (PowerSize.size s)+3)*(s+1) ≤ PowerSize.degree s :=
    by exact_mod_cast hsmallreal
  have hlower := PowerSize.finite_local_round_bound s (rounds (PowerSize.size s)) (by omega)
    (A (PowerSize.size s)) (ν (PowerSize.size s)) (hmeas (PowerSize.size s)) (hcorrect (PowerSize.size s))
  omega

/-- The usual randomized model: each vertex has an independent tape drawn
from the same probability distribution. Tape spaces may contain infinite
bit streams; no finite-support assumption is used. -/
theorem randomized_LOCAL_MIS_iid_not_littleO
    (Tape State : ℕ → Type) [∀ n, MeasurableSpace (Tape n)]
    (rounds : ℕ → ℕ) (A : ∀ n, UniformLocalProtocol n (Tape n) (State n))
    (ρ : ∀ n, Measure (Tape n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (hmeas : ∀ n, MeasurableProgram (A n) (rounds n))
    (hcorrect : ∀ n (G : SimpleGraph (Fin n)),
      (2/3:ℝ) ≤ (Measure.pi (fun _ : Fin n => ρ n)).real
        {W | Maximal G.IsIndepSet ((A n).candidates G id W (rounds n))}) :
    ¬IsLittleO atTop (fun n => (rounds n:ℝ)) localScale := by
  exact randomized_LOCAL_MIS_not_littleO Tape State rounds A
    (fun n => Measure.pi (fun _ : Fin n => ρ n)) hmeas hcorrect

end
end MISLocal


/- ===== Source: Audit.lean ===== -/

/-!
The audit checks transitive dependencies of EVERY theorem in MISLocal and
the public definitions explicitly listed below.
It raises a Lean elaboration error for any axiom beyond the three standard
classical foundations below. A printed success word is never a substitute
for successful compilation. This audit does not assert that a conditional
theorem has had all of its mathematical hypotheses discharged.
-/

open Lean Elab Command

elab "#audit_mislocal" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let definitions : Array Name := #[
    ``MISLocal.bit, ``MISLocal.FiniteProb, ``MISLocal.FiniteProb.expect,
    ``MISLocal.FiniteProb.prob, ``MISLocal.FiniteProb.uniform,
    ``MISLocal.repair, ``MISLocal.Occupies, ``MISLocal.ExternallyDominatable,
    ``MISLocal.completeIDs, ``MISLocal.reindexTapes,
    ``MISLocal.sumSplit, ``MISLocal.jointSumSplit, ``MISLocal.occupancyCap,
    ``MISLocal.FiniteProb.pointMass, ``MISLocal.FiniteProb.map,
    ``MISLocal.FiniteProb.entropy, ``MISLocal.FiniteProb.entropyOf,
    ``MISLocal.FiniteProb.condEntropy, ``MISLocal.FiniteProb.Dominated,
    ``MISLocal.FiniteProb.kl, ``MISLocal.massBudget,
    ``MISLocal.FiniteProb.conditionalProduct, ``MISLocal.FiniteProb.given,
    ``MISLocal.FiniteProb.projectedPair, ``MISLocal.selectedConflict,
    ``MISLocal.classifiedOutput, ``MISLocal.FiniteProb.hellingerSq,
    ``MISLocal.InBall, ``MISLocal.LocalProtocol, ``MISLocal.LocalProtocol.run,
    ``MISLocal.LocalProtocol.candidates, ``MISLocal.UniformLocalProtocol, ``MISLocal.FiniteProb.product,
    ``MISLocal.bestList, ``MISLocal.FiniteProb.outputList, ``MISLocal.FiniteProb.listTail,
    ``MISLocal.FiniteProb.tail, ``MISLocal.FiniteProb.pi, ``MISLocal.FiniteProb.Independent,
    ``MISLocal.FiniteProb.IndependentEvents, ``MISLocal.FiniteProb.eventCount,
    ``MISLocal.FiniteProb.eventMean, ``MISLocal.FiniteProb.labelWeight,
    ``MISLocal.FiniteProb.totalListWeight, ``MISLocal.FiniteProb.listCaptures,
    ``MISLocal.FiniteProb.branchEligible, ``MISLocal.FiniteProb.branchList,
    ``MISLocal.FiniteProb.fairBits, ``MISLocal.FiniteProb.rectangleCount,
    ``MISLocal.FiniteProb.exceptionalMatrix, ``MISLocal.restrictOutput,
    ``MISLocal.FiniteProb.keptOutput, ``MISLocal.FiniteProb.deletedOutput,
    ``MISLocal.binaryEntropy, ``MISLocal.FiniteProb.DoesNotRead,
    ``MISLocal.observeInputs, ``MISLocal.FiniteProb.revealGain,
    ``MISLocal.revealPrefix, ``MISLocal.SourceCharge,
    ``MISLocal.ProductInputGeometry, ``MISLocal.EndpointTransport,
    ``MISLocal.InputRelabeling, ``MISLocal.NamedLocalView,
    ``MISLocal.TreeGeometry.OrientedRegionIso]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  -- Reuse Lean's own traversal state across roots. A dependency already
  -- traversed in this same immutable checked environment need not be visited
  -- again. This changes runtime, not the set of axioms that is checked.
  let mut traversal : CollectAxioms.State := {}
  for (name, info) in env.constants do
    if (`MISLocal).isPrefixOf name &&
        (info.isTheorem || (info.isDefinition && !name.isInternal) || definitions.contains name) then
      unless (env.checked.get.find? name).isSome do
        throwError "Declaration is absent from the checked kernel environment: {name}"
      let (_, next) := ((CollectAxioms.collect name).run env).run traversal
      traversal := next
      for ax in traversal.axioms do
        unless allowed.contains ax do
          throwError "Forbidden axiom dependency: {name} depends on {ax}"
      checked := checked + 1
      if info.isTheorem then
        theorems := theorems + 1
  unless checked > 0 && theorems > 0 do
    throwError "Empty audit: the MISLocal modules were not imported"
  logInfo m!"Audited {checked} theorem/definition roots, including {theorems} theorems."
  logInfo "Only propext, Classical.choice, and Quot.sound were allowed."

#audit_mislocal

#print axioms MISLocal.FiniteTree.graph_edgeRegion_tree
#print axioms MISLocal.realization_forces_repaired_occupancy
#print axioms MISLocal.TreeGeometry.local_size_obstruction
#print axioms MISLocal.PowerSize.finite_local_round_bound
#print axioms MISLocal.randomized_LOCAL_MIS_not_littleO
#print axioms MISLocal.randomized_LOCAL_MIS_iid_not_littleO
#check MISLocal.MeasurableProgram
#check MISLocal.PowerSize.finite_local_round_bound
#check MISLocal.randomized_LOCAL_MIS_iid_not_littleO

#print axioms MISLocal.outgoing_sums_jointly_uniform
#print axioms MISLocal.local_collision_bound_of_pairwise_independent
#print axioms MISLocal.completeIDs_bijective
#print axioms MISLocal.tape_reindex_measurePreserving
#print axioms MISLocal.average_fixed_tape_bound
#print axioms MISLocal.occupancy_transfer
#print axioms MISLocal.finite_obstruction
#print axioms MISLocal.conditional_round_lower_bound
#print axioms MISLocal.FiniteProb.zero_event_le_kl
#print axioms MISLocal.FiniteProb.entropy_submodular
#print axioms MISLocal.FiniteProb.copying_potential_nonincrease
#print axioms MISLocal.FiniteProb.conditional_rare_entropy_le
#print axioms MISLocal.FiniteProb.classified_projected_budget
#print axioms MISLocal.occupancy_from_reduction_estimates
#print axioms MISLocal.FiniteProb.sqrt_event_le
#print axioms MISLocal.completed_ID_simulation
#print axioms MISLocal.zero_radius_conflict
#print axioms MISLocal.FiniteProb.branch_transfer
#print axioms MISLocal.FiniteProb.dense_boolean_tail_product
#print axioms MISLocal.FiniteProb.exceptional_matrix_probability
#print axioms MISLocal.FiniteProb.conditional_edge_vertex_entropy
#print axioms MISLocal.FiniteProb.symmetric_conditional_edge_entropy
#print axioms MISLocal.truncation_moment_bound

/- Print the hypotheses too: checking only the conclusion is insufficient. -/
#check MISLocal.conditional_round_lower_bound
#check MISLocal.FiniteProb.classified_projected_budget
#check MISLocal.occupancy_from_reduction_estimates
#check MISLocal.completed_ID_simulation
#check MISLocal.FiniteProb.branch_transfer
#check MISLocal.FiniteProb.symmetric_conditional_edge_entropy
#print axioms MISLocal.TreeGeometry.sourceChargeOfReaderTrees
#print axioms MISLocal.FiniteProb.symmetric_table_entropy
#print axioms MISLocal.FiniteProb.weighted_branch_failures
#print axioms MISLocal.FiniteProb.ancestor_mass_partition
#check MISLocal.TreeGeometry.sourceChargeOfReaderTrees
#check MISLocal.FiniteProb.symmetric_table_entropy
#check MISLocal.FiniteProb.truncation_from_local_moments
#print axioms MISLocal.FiniteProb.sampled_is_projectedPair
#print axioms MISLocal.FiniteProb.survivor_transport
#print axioms MISLocal.FiniteProb.finite_occupancy
#print axioms MISLocal.TreeGeometry.graphInputGeometry
#print axioms MISLocal.TreeGeometry.graph_occupancy
#print axioms MISLocal.viewHomogeneous_of_input_relabelings
#print axioms MISLocal.TreeGeometry.averaged_graph_occupancy
#print axioms MISLocal.TreeGeometry.graph_finite_obstruction
#check MISLocal.FiniteProb.finite_occupancy
#check MISLocal.TreeGeometry.graph_occupancy
#check MISLocal.TreeGeometry.graph_finite_obstruction
#print axioms MISLocal.TreeGeometry.regularRegionIso
#print axioms MISLocal.TreeGeometry.runAnonymous_zero_same_coin
#print axioms MISLocal.TreeGeometry.anonymous_homogeneous
#print axioms MISLocal.TreeGeometry.anonymous_graph_occupancy
#print axioms MISLocal.TreeGeometry.averaged_anonymous_graph_occupancy
#print axioms MISLocal.TreeGeometry.anonymous_graph_finite_obstruction
#check MISLocal.AnonymousRule
#check MISLocal.TreeGeometry.anonymous_homogeneous
#check MISLocal.TreeGeometry.anonymous_graph_occupancy
#check MISLocal.TreeGeometry.anonymous_graph_finite_obstruction

#print axioms MISLocal.TreeGeometry.extractedIdentifiers_jointly_uniform
#print axioms MISLocal.TreeGeometry.localAnonymousRule_representation
#print axioms MISLocal.TreeGeometry.completed_candidate_simulation
#print axioms MISLocal.TreeGeometry.external_domination_probability
#print axioms MISLocal.TreeGeometry.concrete_finite_obstruction
#check MISLocal.UniformLocalProtocol
#check MISLocal.TreeGeometry.concrete_finite_obstruction


/- ===== Source: Tests.lean ===== -/

/-! Kernel-checked regression examples for boundary cases and repair semantics. -/

open MISLocal

example : (1 - 2 : ℕ) = 0 := by decide
example : (1 : ℝ) - 2 = -1 := by norm_num

example : (0 : ℝ) * ((0 : ℝ) - 1) = 0 := by norm_num
example : (1 : ℝ) * ((1 : ℝ) - 1) = 0 := by norm_num

example (n : ℕ) : ((n - n : ℕ) : ℝ) = 0 := by simp

/-- An edgeless graph really does keep all candidates. -/
example {V : Type*} (S : Set V) : repair (⊥ : SimpleGraph V) S = S := by
  apply repair_of_independent
  intro v hv w hw hne hAdj
  exact hAdj

/-- Two adjacent candidates really are both deleted. -/
example : repair (⊤ : SimpleGraph (Fin 2)) Set.univ = ∅ := by
  ext v
  simp only [repair, Set.mem_setOf_eq, Set.mem_univ, true_and,
    Set.mem_empty_iff_false, iff_false]
  intro h
  fin_cases v
  · exact h 1 (by decide) True.intro
  · exact h 0 (by decide) True.intro

/-- A single coordinate is vacuously collision-free. -/
example {Ω ID : Type*} (X : Fin 1 → Ω → ID) (ω : Ω) :
    Function.Injective (fun i => X i ω) := by
  intro i j _
  exact Subsingleton.elim i j

/-- Empty local views do not require a positive cardinality assumption. -/
example (f : Fin 3 → Fin 3) : Function.Bijective (completeIDs ∅ f) :=
  completeIDs_bijective ∅ f

/-- Collision subtraction is explicitly real; L=0 is not excluded by accident. -/
example : 0 ≤ (0 : ℝ) * ((0 : ℝ) - 1) := by
  norm_num

/-- The round index T+3 does not underflow even at T=0. -/
example : occupancyCap (0 + 3) 10 = min 1 (15000 * Real.log 10 / 10) := by
  norm_num [occupancyCap]

/-- Zero-mass entropy expressions use the continuous extension. -/
example (m : ℝ) : massBudget m 0 = 0 := massBudget_zero m

/-- Logarithm conventions alone do NOT implement infinite relative entropy:
disjoint point masses have real-valued `kl` zero, but are not dominated. -/
example : (FiniteProb.pointMass false).kl (FiniteProb.pointMass true) = 0 := by
  simp [FiniteProb.kl, FiniteProb.pointMass, bit, Fintype.sum_bool]

example : ¬(FiniteProb.pointMass false).Dominated (FiniteProb.pointMass true) := by
  intro h
  have hh := h false (by simp [FiniteProb.pointMass, bit])
  norm_num [FiniteProb.pointMass, bit] at hh

example : (FiniteProb.pointMass true).prob (fun b => b = true) = 1 := by
  simp [bit]

/-- Therefore dropping the support premise from zero_event_le_kl would be false. -/
example : ¬((FiniteProb.pointMass true).prob (fun b => b = true) ≤
    (FiniteProb.pointMass false).kl (FiniteProb.pointMass true)) := by
  simp [FiniteProb.kl, FiniteProb.pointMass, bit, FiniteProb.prob, FiniteProb.expect,
    Fintype.sum_bool]

/-- Conditional entropy of an already-known variable is exactly zero. -/
example (μ : FiniteProb Bool) : μ.condEntropy id id = 0 :=
  μ.condEntropy_deterministic id id

/-- A null conditioning fiber still yields a normalized distribution. -/
example : (FiniteProb.given (FiniteProb.pointMass false) id true).weight false = 1 := by
  simp [FiniteProb.given, FiniteProb.map, FiniteProb.pointMass, FiniteProb.prob,
    FiniteProb.expect, bit, Fintype.sum_bool]

/-- Zero-round local computation sees just the root's input. -/
example {V Input State : Type*} (G : SimpleGraph V) (A : LocalProtocol G Input State)
    (v : V) (x y : V → Input) (h : x v = y v) : A.run x 0 v = A.run y 0 v := by
  exact A.run_local 0 v x y (fun u hu => by cases hu; exact h)

/-- Always selecting the sole available label conflicts on exactly half the matrices. -/
example :
    ((FiniteProb.uniform (Fin 1 × Fin 1 → Bool)).product
      ((FiniteProb.pointMass (some (0 : Fin 1))).product
        (FiniteProb.pointMass (some (0 : Fin 1))))).prob
      (selectedConflict (fun G a b => G (a,b) = true)) = 1/2 := by
  simpa [bit] using zero_radius_conflict (A := Fin 1) (FiniteProb.pointMass (some (0 : Fin 1)))

/-- A list larger than the alphabet has zero omitted mass, even when the
maximizer's tie-breaking does not literally choose every zero-weight label. -/
example (μ : FiniteProb (Option (Fin 2))) : μ.tail 100 = 0 := by
  have h := μ.tail_minimal 100 Finset.univ (by simp)
  have hz : μ.listTail Finset.univ = 0 := by simp [FiniteProb.listTail]
  exact le_antisymm (by simpa only [hz] using h) (μ.listTail_nonneg _)

/-- The graph-radius conversion is only used below the last layer. -/
example (n j : ℕ) (hj : j < n+1) : n+1-j = (n+1-(j+1))+1 := by omega

/-- The last view really contains no raw edges. -/
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (v : V) :
    TreeGeometry.seen G (n+1-(n+1)) v = ∅ := by simp [TreeGeometry.seen]

/-- Adding independent private draws does not reveal them in the final view. -/
example {I V E : Type} [DecidableEq I] [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] {d r : ℕ} (g : ProductInputGeometry I V E d r) (v : V) :
    g.withPrivate.vertex r v = ∅ := g.withPrivate.empty_last v

/-- The strong degree/clique-size regime is not silently applicable to k=1. -/
example (D : ℝ) (hD : 1 ≤ D) : ¬ D ≤ Real.log (1:ℝ) := by
  rw [Real.log_one]
  linarith

/-- Skeleton names 0 and 1 cannot distinguish roots in a zero-round rule.
This test does not assume regularity, graph automorphisms or view symmetry. -/
example (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj]
    (A : AnonymousRule (Fin 2) G.edgeSet 1 Unit)
    (x y : ∀ i, TreeGeometry.matrixPrivateType G 1 (fun _ => Unit) i) :
    TreeGeometry.runAnonymous G A 0 0 x = TreeGeometry.runAnonymous G A 0 1 y :=
  TreeGeometry.runAnonymous_zero_same_coin G A 0 1 x y (by
    change (x (Sum.inr 0) : Unit) = (y (Sum.inr 1) : Unit)
    exact @Subsingleton.elim Unit _ (x (Sum.inr 0)) (y (Sum.inr 1)))

/-- Aaron added the following below -/

#print axioms MISLocal.randomized_LOCAL_MIS_iid_not_littleO
