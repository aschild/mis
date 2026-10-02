import MISLocal.AnySourceEntropy
import MISLocal.ParentCharging
import MISLocal.TableSampling

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
