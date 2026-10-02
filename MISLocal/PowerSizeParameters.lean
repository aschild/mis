import MISLocal.LocalSizeObstruction
import MISLocal.FiniteRegularSkeleton
/-! Explicit finite powers-of-two size, matrix-capacity and probability estimates. -/
open scoped Classical
namespace MISLocal
noncomputable section
namespace PowerSize
def degree (s : ℕ) := 2^s
def halfClique (D : ℕ) := 2^(2*D)
def bits (D : ℕ) := 6*D+1
def size (s : ℕ) := 2^(bits (degree s))
theorem log_two_bounds : (1/2:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h
    exact h
  · have h := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h
    exact h
theorem cube_le_two_pow {D : ℕ} (hD : 10 ≤ D) : D^3 ≤ 2^D := by
  induction D,hD using Nat.le_induction with
  | base => norm_num
  | succ D hD ih =>
    rw [pow_succ (2:ℕ) D]
    have h1 : 10*D ≤ D^2 := by nlinarith [Nat.mul_le_mul_left D hD]
    have h2 : 10*D^2 ≤ D^3 := by nlinarith [Nat.mul_le_mul_left (D*D) hD]
    have hc : (D+1)^3 ≤ 2*D^3 := by nlinarith
    exact hc.trans (by nlinarith)
theorem clique_power (D : ℕ) : 2*halfClique D = 2^(2*D+1) := by
  simp only [halfClique,pow_succ]
  omega
theorem packing_exists {D : ℕ} (hD : 10 ≤ D) :
    Nonempty ((Fin (2*halfClique D) × Fin (bits D)) ↪ (Fin (halfClique D) × Fin (halfClique D))) := by
  apply Function.Embedding.nonempty_of_card_le
  simp only [Fintype.card_prod,Fintype.card_fin]
  have he : D^3 ≤ halfClique D := (cube_le_two_pow hD).trans
    (pow_le_pow_right' (by omega : 1 ≤ (2:ℕ)) (by omega))
  have hm : 2*bits D ≤ halfClique D := by
    have h1 : 10*D ≤ D^2 := by nlinarith [Nat.mul_le_mul_left D hD]
    have h2 : 10*D^2 ≤ D^3 := by nlinarith [Nat.mul_le_mul_left (D*D) hD]
    unfold bits
    nlinarith
  nlinarith
theorem clique_log_bounds {D : ℕ} (hD : 10 ≤ D) :
    (D:ℝ) ≤ Real.log ((2*halfClique D:ℕ):ℝ) ∧
      Real.log ((2*halfClique D:ℕ):ℝ) ≤ (D:ℝ)^2 := by
  rw [clique_power,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  push_cast
  have hd : (10:ℝ) ≤ D := by exact_mod_cast hD
  have hlog := log_two_bounds
  constructor <;> nlinarith
theorem domination_error_small {D : ℕ} (hD : 10 ≤ D) :
    TreeGeometry.localDominationError (m := halfClique D) D ≤ (1/8:ℝ) := by
  let k : ℝ := ((2*halfClique D:ℕ):ℝ)
  have hk : k = (2:ℝ)^(2*D+1) := by
    dsimp only [k]
    rw [clique_power,Nat.cast_pow,Nat.cast_ofNat]
  have hk1 : k+1 ≤ (2:ℝ)^(2*D+2) := by
    rw [hk,show 2*D+2 = (2*D+1)+1 by omega,pow_succ (2:ℝ) (2*D+1)]
    have hone : (1:ℝ) ≤ 2^(2*D+1) := one_le_pow₀ (by norm_num)
    linarith
  have hlog : Real.log (k+1) ≤ (2*(D:ℝ)+2) := by
    have hh := Real.log_le_log (show 0<k+1 by dsimp [k]; positivity) hk1
    rw [Real.log_pow] at hh
    push_cast at hh
    have h2 := log_two_bounds.2
    nlinarith
  have hcancel : k*(2:ℝ)^(-(D:ℤ)) = 2*(2:ℝ)^D := by
    rw [hk,zpow_neg,zpow_natCast,show 2*D+1 = D+D+1 by omega,pow_succ,pow_add]
    have hp : (2:ℝ)^D ≠ 0 := by positivity
    field_simp
    ring
  have hcube : (D:ℝ)^3 ≤ (2:ℝ)^D := by exact_mod_cast cube_le_two_pow hD
  have hd : (10:ℝ) ≤ D := by exact_mod_cast hD
  have hexponent : (D:ℝ)*Real.log (k+1)-k*(2:ℝ)^(-(D:ℤ)) ≤ -(D:ℝ) := by
    rw [hcancel]
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg D)
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg (D:ℝ))]
  have hlog8 : Real.log (8:ℝ) ≤ 3 := by
    have he : Real.log (8:ℝ) = 3*Real.log 2 := by
      rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
      norm_num
    rw [he]
    nlinarith [log_two_bounds.2]
  have hexp : Real.exp (-(D:ℝ)) ≤ (1/8:ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 8) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<8)]; norm_num
  have heq : TreeGeometry.localDominationError (m := halfClique D) D =
      Real.exp ((D:ℝ)*Real.log (k+1)-k*(2:ℝ)^(-(D:ℤ))) := by
    unfold TreeGeometry.localDominationError
    simp only [Nat.cast_add,Nat.cast_one]
    change (k+1)^D*Real.exp (-k*(2:ℝ)^(-(D:ℤ))) = _
    rw [neg_mul,Real.exp_neg,Real.exp_sub,Real.exp_nat_mul (Real.log (k+1)) D,
      Real.exp_log (show 0<k+1 by dsimp [k]; positivity)]
    ring
  rw [heq]
  exact (Real.exp_le_exp.mpr hexponent).trans hexp
end PowerSize
end
end MISLocal
