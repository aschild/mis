import MISLocal.Entropy

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
