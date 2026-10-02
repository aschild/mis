import MISLocal.ProjectedTails
import MISLocal.ConditionalReadLocality

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
