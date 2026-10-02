import MISLocal.RevealedEntropy

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
