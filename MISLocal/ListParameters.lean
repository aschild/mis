import MISLocal.RandomMatrix

/-! One explicit degree threshold for all list and matrix parameters. -/

namespace MISLocal
noncomputable section

def listEll (k : ℕ) : ℕ := ⌈100*Real.log ((k:ℝ)+1)⌉₊
def listMiddle (k : ℕ) : ℕ := 1000*listEll k
def listCapacity (D k : ℕ) : ℕ := D*listMiddle k

theorem log_add_one_le {k : ℝ} (hk : 1 ≤ k) : Real.log (k+1) ≤ Real.log k+1 := by
  have hkp : 0 < k := by linarith
  have h := Real.log_le_log (show 0 < k+1 by linarith) (show k+1 ≤ 2*k by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hkp)] at h
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

theorem listEll_bounds {D : ℝ} {k : ℕ} (hk : 1 ≤ k) (hD : 1 ≤ D)
    (hlower : D ≤ Real.log (k:ℝ)) (hupper : Real.log (k:ℝ) ≤ D^2) :
    100*Real.log (k:ℝ) ≤ (listEll k : ℝ) ∧ (listEll k : ℝ) ≤ 100*D^2+101 := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith
  have hlo := Real.log_le_log hkp (show (k:ℝ) ≤ k+1 by linarith)
  have hceil := Nat.le_ceil (100*Real.log ((k:ℝ)+1))
  have hx : 0 ≤ 100*Real.log ((k:ℝ)+1) := by linarith
  have hceil' := Nat.ceil_lt_add_one hx
  have hlog := log_add_one_le hk'
  change _ ≤ (listEll k : ℝ) at hceil
  change (listEll k : ℝ) < _ at hceil'
  constructor <;> linarith

theorem explicit_list_parameters {D k : ℕ} (hD : 1048576 ≤ D) (hk : 1 ≤ k)
    (hlower : (D:ℝ) ≤ Real.log (k:ℝ)) (hupper : Real.log (k:ℝ) ≤ (D:ℝ)^2) :
    0 < listEll k ∧ 0 < listMiddle k ∧ 0 < listCapacity D k ∧
      32*listEll k ≤ listMiddle k ∧
      (listCapacity D k : ℝ) ≤ (D:ℝ)^4 ∧
      (listMiddle k : ℝ)/(listCapacity D k : ℝ) = 1/(D:ℝ) ∧
      1 ≤ Real.log (D:ℝ) := by
  have hDr : (1048576:ℝ) ≤ D := by exact_mod_cast hD
  have hDp : (0:ℝ) < D := by linarith
  obtain ⟨hell,hell'⟩ := listEll_bounds hk (show (1:ℝ) ≤ D by linarith) hlower hupper
  have hellp : 0 < listEll k := by
    have h : (0:ℝ) < listEll k := by linarith
    exact_mod_cast h
  have hMp : 0 < listMiddle k := Nat.mul_pos (by decide) hellp
  have hDn : 0 < D := by omega
  have hmp : 0 < listCapacity D k := Nat.mul_pos hDn hMp
  have hMu : (listMiddle k : ℝ) ≤ (D:ℝ)^3 := by
    have hm : (listMiddle k : ℝ) ≤ 100000*(D:ℝ)^2+101000 := by
      dsimp [listMiddle]
      push_cast
      linarith
    have hc := mul_le_mul_of_nonneg_right hDr (sq_nonneg (D:ℝ))
    nlinarith [sq_nonneg ((D:ℝ)-1)]
  refine ⟨hellp,hMp,hmp,by dsimp [listMiddle]; omega,?_,?_,?_⟩
  · change ((D*listMiddle k : ℕ):ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      _ ≤ (D:ℝ)*(D:ℝ)^3 := mul_le_mul_of_nonneg_left hMu hDp.le
      _ = _ := by ring
  · have hMne : (listMiddle k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hMp)
    simp only [listCapacity, Nat.cast_mul]
    field_simp
    ring
  · have he := Real.abs_exp_sub_one_le (x := (1:ℝ)) (by norm_num)
    have h3 : Real.exp (1:ℝ) ≤ 3 := by
      have hh := (le_abs_self (Real.exp (1:ℝ)-1)).trans he
      norm_num at hh
      linarith
    have hl := Real.log_le_log (Real.exp_pos (1:ℝ)) (show Real.exp (1:ℝ) ≤ D by linarith)
    simpa using hl

theorem matrix_numeric_bound {D k : ℝ} {ell : ℕ} (hD : 12 ≤ D) (hk : 0 < k)
    (hlower : D ≤ Real.log k) (hell : 100*Real.log k ≤ (ell:ℝ)) :
    k^(2*ell)*Real.exp (-(ell:ℝ)^2/16) ≤ 1/D^2 := by
  have hDp : 0 < D := by linarith
  have hl0 : 0 ≤ Real.log k := by linarith
  have he0 : (0:ℝ) ≤ ell := Nat.cast_nonneg _
  have h64 : 64*Real.log k ≤ (ell:ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_left h64 he0
  have hlogD := Real.log_le_sub_one_of_pos hDp
  have hellsq : 64*Real.log D ≤ (ell:ℝ)^2 := by
    nlinarith [sq_nonneg ((ell:ℝ)-1)]
  calc
    _ = Real.exp ((2*(ell:ℝ))*Real.log k-(ell:ℝ)^2/16) := by
      rw [Real.exp_sub, show Real.exp ((2*(ell:ℝ))*Real.log k) = k^(2*ell) by
        norm_cast; rw [Real.exp_nat_mul, Real.exp_log hk]]
      rw [show -(ell:ℝ)^2/16 = -((ell:ℝ)^2/16) by ring, Real.exp_neg]
      ring
    _ ≤ Real.exp (-(ell:ℝ)^2/32) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ Real.exp (-(2:ℝ)*Real.log D) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := exp_neg_nat_log hDp 2

end
end MISLocal
