import MISLocal.PrivateSources

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
