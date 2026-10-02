import MISLocal.FiniteTreePermutations
import MISLocal.GraphViewTransport
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
