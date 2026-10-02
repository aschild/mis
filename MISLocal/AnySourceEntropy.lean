import MISLocal.EntropyCharging
import MISLocal.SharedViews

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
