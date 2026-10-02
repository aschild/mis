import MISLocal.BranchParameters
import MISLocal.EntropyProduct
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.Powerset

/-! An actual product of independent fair Boolean matrix entries. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω I A B : Type*} [Fintype Ω] [Fintype I] [Fintype A] [Fintype B]

theorem IndependentEvents.half_lower_tail {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) :
    μ.prob (fun ω => eventCount E ω ≤ μ.eventMean E/2) ≤
      Real.exp (-μ.eventMean E/8) := by
  have hnum : Real.exp (-(1:ℝ)) ≤ 3/8 := by
    have hs := Real.sum_le_exp_of_nonneg (x := (1:ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at hs
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    linarith
  have hm := μ.prob_ge_le_expect_div (fun ω => Real.exp (-eventCount E ω))
    (fun ω => (Real.exp_pos _).le) (Real.exp_pos (-μ.eventMean E/2))
  have he := h.exp_expect_le (-(1:ℝ))
  simp only [neg_one_mul] at he
  calc
    _ ≤ μ.prob (fun ω => Real.exp (-μ.eventMean E/2) ≤ Real.exp (-eventCount E ω)) := by
      apply μ.prob_mono
      intro ω hω
      exact Real.exp_le_exp.mpr (by linarith)
    _ ≤ μ.expect (fun ω => Real.exp (-eventCount E ω)) / Real.exp (-μ.eventMean E/2) := hm
    _ ≤ Real.exp ((Real.exp (-1)-1)*μ.eventMean E) / Real.exp (-μ.eventMean E/2) :=
      div_le_div_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp ((Real.exp (-1)-1)*μ.eventMean E + μ.eventMean E/2) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hn := μ.eventMean_nonneg E
      nlinarith)

def fairBits (I : Type*) [Fintype I] [DecidableEq I] : FiniteProb (I → Bool) :=
  pi (fun _ : I => uniform Bool)

theorem fairBits_coordinate [DecidableEq I] (i : I) :
    (fairBits I).prob (fun x => x i = true) = 1/2 := by
  change (pi (fun _ : I => uniform Bool)).expect (fun x => bit (x i = true)) = _
  rw [pi_expect_coordinate (fun _ : I => uniform Bool) i (fun b => bit (b = true))]
  norm_num [uniform, expect, bit, Fintype.sum_bool]

variable [DecidableEq A] [DecidableEq B]

def rectangleCount (S : Finset A) (T : Finset B) (G : A × B → Bool) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ T, bit (G (a,b) = true)

theorem rectangleCount_eq (S : Finset A) (T : Finset B) (G : A × B → Bool) :
    eventCount (fun ab (G : A × B → Bool) => ab.1 ∈ S ∧ ab.2 ∈ T ∧ G ab = true) G =
      rectangleCount S T G := by
  classical
  let E := fun ab : A × B => ab.1 ∈ S ∧ ab.2 ∈ T ∧ G ab = true
  change (∑ ab, bit (E ab)) = _
  have hs := Finset.sum_subset (f := fun ab => bit (E ab)) (Finset.subset_univ (S.product T))
    (fun ab _ hab => by
      have hn : ¬ (ab.1 ∈ S ∧ ab.2 ∈ T) := by simpa using hab
      by_cases ha : ab.1 ∈ S <;> by_cases hb : ab.2 ∈ T <;> simp_all [E, bit])
  rw [← hs]
  calc
    _ = ∑ ab ∈ S.product T, bit (G ab = true) := by
      apply Finset.sum_congr rfl
      intro ab hab
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
      simp [E, ha, hb]
    _ = _ := Finset.sum_product _ _ _

theorem rectangleCount_expect (S : Finset A) (T : Finset B) :
    (fairBits (A × B)).expect (rectangleCount S T) = (S.card : ℝ)*T.card/2 := by
  change (fairBits (A × B)).expect (fun G => ∑ a ∈ S, ∑ b ∈ T, bit (G (a,b) = true)) = _
  rw [expect_sum]
  simp only [expect_sum]
  change (∑ a ∈ S, ∑ b ∈ T, (fairBits (A × B)).prob (fun G => G (a,b) = true)) = _
  simp [fairBits_coordinate]
  ring

theorem rectangle_sparse_probability (S : Finset A) (T : Finset B) :
    (fairBits (A × B)).prob (fun G => rectangleCount S T G ≤ (S.card : ℝ)*T.card/4) ≤
      Real.exp (-((S.card : ℝ)*T.card)/16) := by
  let E := fun ab : A × B => fun G : A × B → Bool => ab.1 ∈ S ∧ ab.2 ∈ T ∧ G ab = true
  have hind : (fairBits (A × B)).IndependentEvents E :=
    (pi_independent (fun _ : A × B => uniform Bool)).events
      (fun ab b => ab.1 ∈ S ∧ ab.2 ∈ T ∧ b = true)
  have hmean : (fairBits (A × B)).eventMean E = (S.card : ℝ)*T.card/2 := by
    rw [← expect_eventCount]
    have he : eventCount E = rectangleCount S T := funext (rectangleCount_eq S T)
    rw [he, rectangleCount_expect]
  have h := hind.half_lower_tail
  simp only [hmean, E, rectangleCount_eq] at h
  convert h using 1 <;> congr 1 <;> first | (funext G; congr 1; ring) | ring

def exceptionalMatrix (ell : ℕ) (G : A × A → Bool) : Prop :=
  ∃ S : {S : Finset A // S.card = ell}, ∃ T : {T : Finset A // T.card = ell},
    rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4

theorem exceptional_matrix_probability (ell : ℕ) :
    (fairBits (A × A)).prob (exceptionalMatrix (A := A) ell) ≤
      (Fintype.card A : ℝ)^(2*ell) * Real.exp (-(ell : ℝ)^2/16) := by
  let μ := fairBits (A × A)
  let sides := {S : Finset A // S.card = ell}
  let q := Real.exp (-(ell : ℝ)^2/16)
  have hpair (S T : sides) : μ.prob (fun G => rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4) ≤ q := by
    have h := rectangle_sparse_probability S.val T.val
    simpa [S.property, T.property, pow_two, q, μ] using h
  have hfirst := μ.prob_exists_le_sum (fun S : sides => fun G =>
    ∃ T : sides, rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4)
  have hsecond (S : sides) := μ.prob_exists_le_sum (fun T : sides => fun G =>
    rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4)
  have hc : (Fintype.card sides : ℝ) ≤ (Fintype.card A : ℝ)^ell := by
    dsimp [sides]
    rw [Fintype.card_finset_len]
    exact_mod_cast Nat.choose_le_pow (Fintype.card A) ell
  calc
    _ ≤ ∑ S : sides, ∑ T : sides,
        μ.prob (fun G => rectangleCount S.val T.val G ≤ (ell : ℝ)^2/4) :=
      hfirst.trans (Finset.sum_le_sum (fun S _ => hsecond S))
    _ ≤ ∑ _S : sides, ∑ _T : sides, q :=
      Finset.sum_le_sum (fun S _ => Finset.sum_le_sum (fun T _ => hpair S T))
    _ = (Fintype.card sides : ℝ)^2*q := by simp; ring
    _ ≤ ((Fintype.card A : ℝ)^ell)^2*q := by gcongr
    _ = _ := by rw [← pow_mul, Nat.mul_comm ell 2]

end FiniteProb
end
end MISLocal
