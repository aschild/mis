import MISLocal.EntropyBudget
import MISLocal.Numerics
import Mathlib.Data.Real.Sqrt

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
