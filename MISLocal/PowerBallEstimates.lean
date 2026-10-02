import MISLocal.PowerSizeParameters
/-! Ball capacity and the collision error for the explicit parameter sequence. -/
open scoped Classical
namespace MISLocal
noncomputable section
namespace PowerSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s T : ℕ} (hreg : ∀ v, G.degree v ≤ degree s)

include hreg in
theorem ball_square_fit (root : V)
    (hsmall : 20000*(T+3)*(s+1) ≤ degree s) :
    8*((ballFinset G (T+2) root).card*(2*halfClique (degree s)))^2 ≤ size s := by
  let D := degree s
  let E := (s+1)*(T+2)+(2*D+1)
  have hD : 1 ≤ D := Nat.one_le_pow _ _ (by norm_num)
  have hb := ballFinset_card_le G hreg (T+2) root
  have hplus : D+1 ≤ 2^(s+1) := by
    change 2^s+1 ≤ 2^(s+1)
    rw [pow_succ]
    change 1 ≤ 2^s at hD
    omega
  have hL : (ballFinset G (T+2) root).card*(2*halfClique D) ≤ 2^E := by
    calc
      _ ≤ (D+1)^(T+2)*(2*halfClique D) := Nat.mul_le_mul_right _ hb
      _ ≤ (2^(s+1))^(T+2)*(2*halfClique D) :=
        Nat.mul_le_mul_right _ (pow_le_pow_left' hplus (T+2))
      _ = 2^E := by rw [clique_power,← pow_mul,← pow_add]
  have he : 2*E+3 ≤ bits D := by
    have hs : 20000*((s+1)*(T+3)) ≤ D := by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hsmall
    have hmin : 3 ≤ (s+1)*(T+3) := by nlinarith
    have hmon : (s+1)*(T+2) ≤ (s+1)*(T+3) := Nat.mul_le_mul_left _ (by omega)
    dsimp only [E,bits]
    nlinarith
  calc
    _ ≤ 8*(2^E)^2 := Nat.mul_le_mul_left _ (pow_le_pow_left' hL 2)
    _ = 2^(2*E+3) := by rw [← pow_mul,Nat.mul_comm E 2,pow_add]; norm_num; ring
    _ ≤ 2^(bits D) := pow_le_pow_right' (by norm_num) he

include hreg in
theorem ball_fits (root : V) (hsmall : 20000*(T+3)*(s+1) ≤ degree s) :
    (ballFinset G (T+2) root).card*(2*halfClique (degree s)) ≤ size s := by
  have h := ball_square_fit G hreg root hsmall
  have hl : ∀ L : ℕ, L ≤ 8*L^2 := by intro L; nlinarith
  exact (hl _).trans h

include hreg in
theorem collision_error_small (root : V) (hsmall : 20000*(T+3)*(s+1) ≤ degree s) :
    TreeGeometry.localCollisionError G (m := halfClique (degree s)) (b := bits (degree s)) T root ≤ (1/8:ℝ) := by
  let L := (ballFinset G (T+2) root).card*(2*halfClique (degree s))
  have hnat := ball_square_fit G hreg root hsmall
  have h : (8:ℝ)*(L:ℝ)^2 ≤ (size s:ℝ) := by exact_mod_cast hnat
  have hn : (0:ℝ) < size s := by dsimp only [size]; positivity
  change (L:ℝ)*((L:ℝ)-1)/(size s:ℝ) ≤ _
  apply (div_le_iff₀ hn).mpr
  have hL : (0:ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith

theorem small_occupancy_cap {s T : ℕ} (hsmall : 20000*(T+3)*(s+1) ≤ degree s) :
    occupancyCap (T+3) (degree s:ℝ) ≤ (1/4:ℝ) := by
  have hd : (0:ℝ) < degree s := by dsimp only [degree]; positivity
  have hs : (20000:ℝ)*((T:ℝ)+3)*((s:ℝ)+1) ≤ (degree s:ℝ) := by exact_mod_cast hsmall
  have he : Real.log (degree s:ℝ) = (s:ℝ)*Real.log 2 := by
    simp only [degree,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  unfold occupancyCap
  apply (min_le_right _ _).trans
  apply (div_le_iff₀ hd).mpr
  rw [he]
  push_cast
  have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hS : (0:ℝ) ≤ s := Nat.cast_nonneg _
  have hlog := mul_le_mul_of_nonneg_left log_two_bounds.2
    (show 0 ≤ 5000*((T:ℝ)+3)*(s:ℝ) by positivity)
  nlinarith
end PowerSize
end
end MISLocal
