import MISLocal.RandomMatrix
import MISLocal.Truncation

/-! Averaging the dense-matrix estimate on genuine conditional fibers. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

theorem product_selected_probability (P : FiniteProb (Option A))
    (Q : FiniteProb (Option B)) (G : A → B → Prop) :
    (P.product Q).prob (fun ab => selectedConflict (fun _ : Unit => G) ((),ab.1,ab.2)) =
      ∑ a, ∑ b, P.weight (some a) * Q.weight (some b) * bit (G a b) := by
  simp only [prob, expect, product, Fintype.sum_prod_type, Fintype.sum_option, selectedConflict,
    bit_false, mul_zero, Finset.sum_const_zero, zero_add]

theorem matrix_tail_product [DecidableEq A] (P Q : FiniteProb (Option A))
    (G : A × A → Bool) {ell : ℕ} (hell : 0 < ell) :
    P.tail ell * Q.tail ell ≤
      4*(P.product Q).prob (fun ab => selectedConflict (fun _ : Unit => fun a b => G (a,b) = true)
        ((),ab.1,ab.2)) + bit (exceptionalMatrix ell G) := by
  by_cases hbad : exceptionalMatrix ell G
  · rw [show bit (exceptionalMatrix ell G) = 1 by simp [bit, hbad]]
    have hp := P.listTail_le_one (P.outputList ell)
    have hq := Q.listTail_le_one (Q.outputList ell)
    have hq0 := Q.listTail_nonneg (Q.outputList ell)
    have hm := mul_le_mul hp hq hq0 (by norm_num : (0:ℝ) ≤ 1)
    have he := (P.product Q).prob_nonneg
      (fun ab => selectedConflict (fun _ : Unit => fun a b => G (a,b) = true) ((),ab.1,ab.2))
    change P.tail ell*Q.tail ell ≤ 1*1 at hm
    linarith
  · rw [show bit (exceptionalMatrix ell G) = 0 by simp [bit, hbad], add_zero,
      product_selected_probability]
    apply dense_boolean_tail_product P Q (fun a b => G (a,b) = true) hell
    intro S hS T hT
    have hd : ¬ rectangleCount S T G ≤ (ell : ℝ)^2/4 :=
      fun h => hbad ⟨⟨S,hS⟩,⟨T,hT⟩,h⟩
    exact (lt_of_not_ge hd).le

/-- Endpoint outputs may depend on the central matrix. The only required
independence is their conditional independence given the shared view `F`.
Null fibers are handled by zero weights rather than assumed absent. -/
theorem conditional_endpoint_tails [DecidableEq A] (μ : FiniteProb Ω)
    (U V : Ω → Option A) (F : Ω → C) (G : C → A × A → Bool)
    {ell : ℕ} (hell : 0 < ell) {q : ℝ}
    (hind : ∀ b, 0 < (μ.map F).weight b →
      (μ.given F b).map (fun ω => (U ω,V ω)) =
        ((μ.given F b).map U).product ((μ.given F b).map V))
    (hbad : μ.prob (fun ω => exceptionalMatrix ell (G (F ω))) ≤ q) :
    μ.expect (fun ω => ((μ.given F (F ω)).map U).tail ell *
      ((μ.given F (F ω)).map V).tail ell) ≤
      4*μ.prob (fun ω => selectedConflict (fun b a a' => G b (a,a') = true) (F ω,U ω,V ω)) + q := by
  let conflict := fun ω => selectedConflict (fun b a a' => G b (a,a') = true) (F ω,U ω,V ω)
  have hpoint (b : C) (hb : 0 < (μ.map F).weight b) :
      ((μ.given F b).map U).tail ell*((μ.given F b).map V).tail ell ≤
        4*(μ.given F b).prob conflict + bit (exceptionalMatrix ell (G b)) := by
    have he := matrix_tail_product ((μ.given F b).map U) ((μ.given F b).map V) (G b) hell
    rw [← hind b hb, prob_map] at he
    have hc : (μ.given F b).prob conflict =
        (μ.given F b).prob (fun ω => selectedConflict (fun _ : Unit => fun a a' => G b (a,a') = true)
          ((),U ω,V ω)) := by
      apply μ.given_prob_congr F b hb
      intro ω hω
      simp only [conflict, hω, selectedConflict]
    rwa [hc]
  have hmean : (μ.map F).expect (fun b => (μ.given F b).prob conflict) = μ.prob conflict :=
    μ.total_conditional_expectation F (fun ω => bit (conflict ω))
  have hsum := (μ.map F).expect_mono_on_support _ _ hpoint
  rw [expect_add, expect_mul, hmean] at hsum
  change (μ.map F).expect (fun b => ((μ.given F b).map U).tail ell*((μ.given F b).map V).tail ell) ≤
    4*μ.prob conflict + (μ.map F).prob (fun b => exceptionalMatrix ell (G b)) at hsum
  rw [expect_map, prob_map] at hsum
  linarith

end FiniteProb
end
end MISLocal
