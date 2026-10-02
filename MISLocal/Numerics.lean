import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Numerical consequences and subtraction guardrails

These are generic scalar consequences. The finite skeleton construction,
parameter estimates and full asymptotic conclusion are supplied in the
FiniteRegularSkeleton, PowerSize and AsymptoticLocalLowerBound modules.
-/

namespace MISLocal
noncomputable section

def occupancyCap (r : ℕ) (D : ℝ) : ℝ := min 1 (5000 * (r : ℝ) * Real.log D / D)

theorem obstruction_at_least_half {ε δ γ : ℝ}
    (hε : ε ≤ 1 / 3) (herrors : δ + γ ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ (1 - ε) * (1 - δ - γ) := by
  have h1 : (2 / 3 : ℝ) ≤ 1 - ε := by linarith
  have h2 : (3 / 4 : ℝ) ≤ 1 - δ - γ := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- Round lower bound in the degree parameter. The subtraction is in ℝ. -/
theorem degree_round_lower_bound {T : ℕ} {D ε δ γ : ℝ}
    (hD : 1 < D) (hε : ε ≤ 1 / 3) (herrors : δ + γ ≤ 1 / 4)
    (hobstruction : (1 - ε) * (1 - δ - γ) ≤ occupancyCap (T + 3) D) :
    D / (10000 * Real.log D) - 3 ≤ (T : ℝ) := by
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hcap : (1 / 2 : ℝ) ≤ 5000 * ((T : ℝ) + 3) * Real.log D / D := by
    have h := (obstruction_at_least_half hε herrors).trans hobstruction
    exact h.trans (by simp only [occupancyCap, Nat.cast_add, Nat.cast_ofNat]; exact min_le_right _ _)
  have hmul := (le_div_iff₀ hD0).mp hcap
  have hden : 0 < 10000 * Real.log D := by positivity
  have hratio : D / (10000 * Real.log D) ≤ (T : ℝ) + 3 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

/-- The explicit 100000 constant follows from the finite obstruction and these
stated degree/size estimates. Establishing the estimates for all large n, and
constructing the required skeletons, are outside this theorem. -/
theorem size_round_lower_bound {T : ℕ} {D n ε δ γ : ℝ}
    (hD : 1 < D)
    (hDlower : Real.log n / 5 ≤ D)
    (hDupper : D ≤ Real.log n)
    (hlarge : 3 ≤ Real.log n / (100000 * Real.log (Real.log n)))
    (hε : ε ≤ 1 / 3) (herrors : δ + γ ≤ 1 / 4)
    (hobstruction : (1 - ε) * (1 - δ - γ) ≤ occupancyCap (T + 3) D) :
    Real.log n / (100000 * Real.log (Real.log n)) ≤ (T : ℝ) := by
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hn1 : 1 < Real.log n := lt_of_lt_of_le hD hDupper
  have hlogn : 0 < Real.log n := lt_trans zero_lt_one hn1
  have hloglog : 0 < Real.log (Real.log n) := Real.log_pos hn1
  have hlogs : Real.log D ≤ Real.log (Real.log n) :=
    Real.log_le_log (lt_trans zero_lt_one hD) hDupper
  have hbase := degree_round_lower_bound hD hε herrors hobstruction
  have hfrac : 2 * (Real.log n / (100000 * Real.log (Real.log n))) ≤
      D / (10000 * Real.log D) := by
    calc
      _ = (Real.log n / 5) / (10000 * Real.log (Real.log n)) := by ring
      _ ≤ D / (10000 * Real.log (Real.log n)) :=
        div_le_div_of_nonneg_right hDlower (by positivity)
      _ ≤ D / (10000 * Real.log D) :=
        div_le_div_of_nonneg_left (le_of_lt (lt_trans zero_lt_one hD))
          (by positivity) (by nlinarith)
  linarith

/-- The paper's local-collision numerator, with no truncated subtraction. -/
theorem collision_numerator_nonnegative (L : ℕ) :
    0 ≤ (L : ℝ) * ((L : ℝ) - 1) := by
  cases L with
  | zero => norm_num
  | succ L => have h : (0 : ℝ) ≤ L := Nat.cast_nonneg L; push_cast; nlinarith

/-- Casting a genuine natural difference needs the displayed order hypothesis. -/
theorem cast_padding {n k N : ℕ} (hfit : k * N ≤ n) :
    ((n - k * N : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) * (N : ℝ) := by
  rw [Nat.cast_sub hfit, Nat.cast_mul]

end
end MISLocal
