import MISLocal.TopLists
import MISLocal.ZeroRadius

/-!
# Independent finite inputs and exponential estimates

Independence here means factorization of expectations of products. It is proved
for the actual product distribution, including dependent finite coordinate
types. Event independence is the corresponding identity for every subfamily.
-/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

def pi {A : I → Type*} [DecidableEq I] [∀ i, Fintype (A i)]
    (P : ∀ i, FiniteProb (A i)) : FiniteProb (∀ i, A i) where
  weight x := ∏ i, (P i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp only [(P _).total, Finset.prod_const_one]

theorem expect_pi_prod {A : I → Type*} [DecidableEq I] [∀ i, Fintype (A i)]
    (P : ∀ i, FiniteProb (A i)) (f : ∀ i, A i → ℝ) :
    (pi P).expect (fun x => ∏ i, f i (x i)) = ∏ i, (P i).expect (f i) := by
  simp only [expect, pi, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).weight a * f i a)).symm

def Independent {A : I → Type*} (μ : FiniteProb Ω) (X : ∀ i, Ω → A i) : Prop :=
  ∀ f : ∀ i, A i → ℝ, μ.expect (fun ω => ∏ i, f i (X i ω)) =
    ∏ i, μ.expect (fun ω => f i (X i ω))

theorem pi_expect_coordinate {A : I → Type*} [DecidableEq I] [∀ i, Fintype (A i)]
    (P : ∀ i, FiniteProb (A i)) (i : I) (f : A i → ℝ) :
    (pi P).expect (fun x => f (x i)) = (P i).expect f := by
  classical
  let g : ∀ j, A j → ℝ := fun j => if h : j = i then fun a => f (h ▸ a) else fun _ => 1
  have hg (x : ∀ j, A j) : (∏ j, g j (x j)) = f (x i) := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro b _ hb
      simp [g, hb]
    · simp
  have he : (∏ j, (P j).expect (g j)) = (P i).expect f := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro b _ hb
      simp [g, hb]
    · simp
  rw [← he, ← expect_pi_prod P g]
  exact (pi P).expect_congr (fun x => (hg x).symm)

theorem pi_independent {A : I → Type*} [DecidableEq I] [∀ i, Fintype (A i)]
    (P : ∀ i, FiniteProb (A i)) : (pi P).Independent (fun i x => x i) := by
  intro f
  simp only [pi_expect_coordinate, expect_pi_prod]

theorem Independent.comp {A B : I → Type*} {μ : FiniteProb Ω}
    {X : ∀ i, Ω → A i} (h : μ.Independent X) (f : ∀ i, A i → B i) :
    μ.Independent (fun i ω => f i (X i ω)) := by
  intro g
  exact h (fun i a => g i (f i a))

def IndependentEvents (μ : FiniteProb Ω) (E : I → Ω → Prop) : Prop :=
  ∀ s : Finset I, μ.expect (fun ω => ∏ i ∈ s, bit (E i ω)) =
    ∏ i ∈ s, μ.prob (E i)

theorem Independent.events {A : I → Type*} {μ : FiniteProb Ω}
    {X : ∀ i, Ω → A i} (h : μ.Independent X) (E : ∀ i, A i → Prop) :
    μ.IndependentEvents (fun i ω => E i (X i ω)) := by
  intro s
  have hh := h (fun i a => if i ∈ s then bit (E i a) else 1)
  have hx (i : I) : μ.expect (fun ω => if i ∈ s then bit (E i (X i ω)) else 1) =
      if i ∈ s then μ.prob (fun ω => E i (X i ω)) else 1 := by
    by_cases hi : i ∈ s <;> simp [hi, prob]
  simpa only [hx, Finset.prod_ite_mem, Finset.inter_univ, Finset.univ_inter] using hh

theorem IndependentEvents.affine {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) (c : I → ℝ) :
    μ.expect (fun ω => ∏ i, (1 + c i * bit (E i ω))) =
      ∏ i, (1 + c i * μ.prob (E i)) := by
  simp only [Finset.prod_one_add]
  rw [μ.expect_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.prod_mul_distrib, μ.expect_mul, h s]

def eventCount (E : I → Ω → Prop) (ω : Ω) : ℝ := ∑ i, bit (E i ω)

def eventMean (μ : FiniteProb Ω) (E : I → Ω → Prop) : ℝ := ∑ i, μ.prob (E i)

theorem eventMean_nonneg (μ : FiniteProb Ω) (E : I → Ω → Prop) :
    0 ≤ μ.eventMean E := Finset.sum_nonneg (fun i _ => μ.prob_nonneg (E i))

theorem expect_eventCount (μ : FiniteProb Ω) (E : I → Ω → Prop) :
    μ.expect (eventCount E) = μ.eventMean E := μ.expect_sum _ _

theorem IndependentEvents.exp_expect {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) (t : ℝ) :
    μ.expect (fun ω => Real.exp (t * eventCount E ω)) =
      ∏ i, (1 + (Real.exp t - 1) * μ.prob (E i)) := by
  have he (ω : Ω) : Real.exp (t * eventCount E ω) =
      ∏ i, (1 + (Real.exp t - 1) * bit (E i ω)) := by
    simp only [eventCount, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : E i ω <;> simp [bit, hi]
  rw [μ.expect_congr he]
  exact h.affine _

theorem IndependentEvents.exp_expect_le {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) (t : ℝ) :
    μ.expect (fun ω => Real.exp (t * eventCount E ω)) ≤
      Real.exp ((Real.exp t - 1) * μ.eventMean E) := by
  rw [h.exp_expect]
  calc
    _ ≤ ∏ i, Real.exp ((Real.exp t - 1) * μ.prob (E i)) := by
      apply Finset.prod_le_prod
      · intro i _
        have hp := μ.prob_nonneg (E i)
        have hp' := μ.prob_le_one (E i)
        nlinarith [mul_nonneg (Real.exp_pos t).le hp]
      · intro i _
        linarith [Real.add_one_le_exp ((Real.exp t - 1) * μ.prob (E i))]
    _ = _ := by rw [← Real.exp_sum]; simp [eventMean, Finset.mul_sum]

/-- Markov's inequality with a strictly positive real threshold. -/
theorem prob_ge_le_expect_div (μ : FiniteProb Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {a : ℝ} (ha : 0 < a) :
    μ.prob (fun ω => a ≤ f ω) ≤ μ.expect f / a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm, prob, ← μ.expect_mul]
  exact μ.expect_mono (fun ω => by
    by_cases h : a ≤ f ω <;> simp [bit, h, hf ω, h])

/-- A lower-tail Chernoff bound, with the explicit constant used in the
short-list consolidation argument. No independence of outputs is needed. -/
theorem IndependentEvents.lower_tail {μ : FiniteProb Ω} {E : I → Ω → Prop}
    (h : μ.IndependentEvents E) :
    μ.prob (fun ω => eventCount E ω < 7 * μ.eventMean E / 8) ≤
      Real.exp (-μ.eventMean E / 128) := by
  have hnum : Real.exp (-(1:ℝ)/8) ≤ 113/128 := by
    have hq := Real.quadratic_le_exp_of_nonneg (x := (1:ℝ)/8) (by norm_num)
    have hp := Real.exp_pos ((1:ℝ)/8)
    rw [show -(1:ℝ)/8 = -((1:ℝ)/8) by ring, Real.exp_neg]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hmono : μ.prob (fun ω => eventCount E ω < 7 * μ.eventMean E / 8) ≤
      μ.prob (fun ω => Real.exp (-(7 * μ.eventMean E / 8)/8) ≤
        Real.exp (-eventCount E ω/8)) := by
    apply μ.prob_mono
    intro ω hω
    exact Real.exp_le_exp.mpr (by linarith)
  have hm := μ.prob_ge_le_expect_div (fun ω => Real.exp (-eventCount E ω/8))
    (fun ω => (Real.exp_pos _).le) (Real.exp_pos (-(7 * μ.eventMean E / 8)/8))
  have he := h.exp_expect_le (-(1:ℝ)/8)
  have he' : μ.expect (fun ω => Real.exp (-eventCount E ω/8)) ≤
      Real.exp ((Real.exp (-(1:ℝ)/8)-1)*μ.eventMean E) := by
    convert he using 1
    congr 1
    funext ω
    congr 1
    ring
  calc
    _ ≤ _ := hmono.trans hm
    _ ≤ Real.exp ((Real.exp (-(1:ℝ)/8)-1)*μ.eventMean E) /
        Real.exp (-(7*μ.eventMean E/8)/8) :=
      div_le_div_of_nonneg_right he' (Real.exp_pos _).le
    _ = Real.exp (((Real.exp (-(1:ℝ)/8)-1)+7/64)*μ.eventMean E) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hn := μ.eventMean_nonneg E
      nlinarith)

end FiniteProb
end
end MISLocal
