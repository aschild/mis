import MISLocal.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

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
