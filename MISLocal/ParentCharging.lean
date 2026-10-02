import MISLocal.EntropyCharging

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
