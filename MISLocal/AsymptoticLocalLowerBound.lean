import MISLocal.FiniteLocalLowerBound
import Mathlib.Analysis.Asymptotics.Defs

/-! The asymptotic randomized LOCAL MIS lower bound. The program, its state
space and tape distribution may depend on n. Correctness on every n-vertex
graph is required with probability at least 2/3. -/

open MeasureTheory Filter Asymptotics
open scoped Classical Topology
namespace MISLocal
noncomputable section

def localScale (n : ℕ) : ℝ := Real.log (n:ℝ)/Real.log (Real.log (n:ℝ))

namespace PowerSize
theorem size_gt_index (s : ℕ) : s < size s := by
  have h1 : s < degree s := Nat.lt_two_pow_self
  have h2 : degree s ≤ bits (degree s) := by unfold bits; omega
  have h3 : bits (degree s) < size s := Nat.lt_two_pow_self
  omega

theorem size_tendsto : Tendsto size atTop atTop := by
  apply tendsto_atTop.2
  intro n
  exact eventually_atTop.2 ⟨n,fun s hs => hs.trans (size_gt_index s).le⟩

theorem scale_upper {s : ℕ} (hs : 1 ≤ s) :
    0 ≤ localScale (size s) ∧ localScale (size s) ≤ 28*(degree s:ℝ)/((s:ℝ)+1) := by
  have hd : (0:ℝ) < degree s := by unfold degree; positivity
  have hsreal : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hln : (degree s:ℝ) ≤ Real.log (size s:ℝ) ∧
      Real.log (size s:ℝ) ≤ 7*(degree s:ℝ) := by
    rw [size,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    simp only [bits,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    have hd1 : (1:ℝ) ≤ degree s := by exact_mod_cast Nat.one_le_pow s (2:ℕ) (by norm_num)
    constructor <;> nlinarith [log_two_bounds.1,log_two_bounds.2]
  have hll : ((s:ℝ)+1)/4 ≤ Real.log (Real.log (size s:ℝ)) := by
    have hm := Real.log_le_log hd hln.1
    have he : Real.log (degree s:ℝ) = (s:ℝ)*Real.log 2 := by
      simp only [degree,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    rw [he] at hm
    have hh := mul_le_mul_of_nonneg_left log_two_bounds.1 (Nat.cast_nonneg s)
    nlinarith
  have hden : (0:ℝ) < ((s:ℝ)+1)/4 := by positivity
  have hllpos : 0 < Real.log (Real.log (size s:ℝ)) := hden.trans_le hll
  constructor
  · exact div_nonneg (hd.le.trans hln.1) hllpos.le
  · calc
      _ ≤ Real.log (size s:ℝ)/(((s:ℝ)+1)/4) := div_le_div_of_nonneg_left
        (hd.le.trans hln.1) hden hll
      _ ≤ (7*(degree s:ℝ))/(((s:ℝ)+1)/4) := div_le_div_of_nonneg_right hln.2 hden.le
      _ = _ := by field_simp; ring

theorem additive_slack {s : ℕ} (hs : 1000 ≤ s) : 240000*(s+1) ≤ degree s := by
  have hcube := cube_le_two_pow (by omega : 10 ≤ s)
  have h1 : 1000*s ≤ s^2 := by nlinarith [Nat.mul_le_mul_left s hs]
  have h2 : 1000*s^2 ≤ s^3 := by nlinarith [Nat.mul_le_mul_left (s*s) hs]
  exact le_trans (by nlinarith) hcube
end PowerSize

/-- No measurable uniform randomized LOCAL MIS algorithm family has
o(log n / log log n) worst-case rounds. The proof is valid for arbitrary
probability distributions on the tape tables, including independent infinite tapes. -/
theorem randomized_LOCAL_MIS_not_littleO
    (Tape State : ℕ → Type) [∀ n, MeasurableSpace (Tape n)]
    (rounds : ℕ → ℕ) (A : ∀ n, UniformLocalProtocol n (Tape n) (State n))
    (ν : ∀ n, Measure (Fin n → Tape n)) [∀ n, IsProbabilityMeasure (ν n)]
    (hmeas : ∀ n, MeasurableProgram (A n) (rounds n))
    (hcorrect : ∀ n (G : SimpleGraph (Fin n)),
      (2/3:ℝ) ≤ (ν n).real {W | Maximal G.IsIndepSet ((A n).candidates G id W (rounds n))}) :
    ¬IsLittleO atTop (fun n => (rounds n:ℝ)) localScale := by
  intro ho
  have hseq := ho.comp_tendsto PowerSize.size_tendsto
  have hbound := isLittleO_iff.mp hseq (c := (1/2240000:ℝ)) (by norm_num)
  obtain ⟨s,hb,hs⟩ := (hbound.and (eventually_ge_atTop (1000:ℕ))).exists
  have hscale := PowerSize.scale_upper (by omega : 1 ≤ s)
  have hb' : (rounds (PowerSize.size s):ℝ) ≤
      (1/2240000:ℝ)*localScale (PowerSize.size s) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,
      abs_of_nonneg (show (0:ℝ)≤(rounds (PowerSize.size s):ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg hscale.1] using hb
  have hround : (rounds (PowerSize.size s):ℝ) ≤
      (PowerSize.degree s:ℝ)/(80000*((s:ℝ)+1)) := by
    have hu := hb'.trans (mul_le_mul_of_nonneg_left hscale.2 (by norm_num : (0:ℝ)≤1/2240000))
    have he : (PowerSize.degree s:ℝ)/(80000*((s:ℝ)+1)) =
        (1/2240000:ℝ)*(28*(PowerSize.degree s:ℝ)/((s:ℝ)+1)) := by field_simp; ring
    rw [he]
    exact hu
  have hm := (le_div_iff₀ (show (0:ℝ)<80000*((s:ℝ)+1) by positivity)).mp hround
  have ha : (240000:ℝ)*((s:ℝ)+1) ≤ (PowerSize.degree s:ℝ) :=
    by exact_mod_cast PowerSize.additive_slack hs
  have hsmallreal : (20000:ℝ)*((rounds (PowerSize.size s):ℝ)+3)*((s:ℝ)+1) ≤ (PowerSize.degree s:ℝ) := by
    nlinarith
  have hsmall : 20000*(rounds (PowerSize.size s)+3)*(s+1) ≤ PowerSize.degree s :=
    by exact_mod_cast hsmallreal
  have hlower := PowerSize.finite_local_round_bound s (rounds (PowerSize.size s)) (by omega)
    (A (PowerSize.size s)) (ν (PowerSize.size s)) (hmeas (PowerSize.size s)) (hcorrect (PowerSize.size s))
  omega

/-- The usual randomized model: each vertex has an independent tape drawn
from the same probability distribution. Tape spaces may contain infinite
bit streams; no finite-support assumption is used. -/
theorem randomized_LOCAL_MIS_iid_not_littleO
    (Tape State : ℕ → Type) [∀ n, MeasurableSpace (Tape n)]
    (rounds : ℕ → ℕ) (A : ∀ n, UniformLocalProtocol n (Tape n) (State n))
    (ρ : ∀ n, Measure (Tape n)) [∀ n, IsProbabilityMeasure (ρ n)]
    (hmeas : ∀ n, MeasurableProgram (A n) (rounds n))
    (hcorrect : ∀ n (G : SimpleGraph (Fin n)),
      (2/3:ℝ) ≤ (Measure.pi (fun _ : Fin n => ρ n)).real
        {W | Maximal G.IsIndepSet ((A n).candidates G id W (rounds n))}) :
    ¬IsLittleO atTop (fun n => (rounds n:ℝ)) localScale := by
  exact randomized_LOCAL_MIS_not_littleO Tape State rounds A
    (fun n => Measure.pi (fun _ : Fin n => ρ n)) hmeas hcorrect

end
end MISLocal
