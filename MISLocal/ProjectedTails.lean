import MISLocal.FiniteKernels
import MISLocal.EndpointTails

/-! Dense-tail control after projection. The original endpoint outputs may
remain correlated beyond the shared view. Only the two current input views
must be conditionally independent. This is what permits arbitrarily many
ancestor restrictions without pretending that they remain low-radius draws. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

omit [Fintype B] in
theorem Independent.bool_product {Y : Bool → Ω → B} {μ : FiniteProb Ω}
    (h : μ.Independent Y) (f g : B → ℝ) :
    μ.expect (fun ω => f (Y false ω)*g (Y true ω)) =
      μ.expect (fun ω => f (Y false ω))*μ.expect (fun ω => g (Y true ω)) := by
  have he := h (fun b => if b then g else f)
  simpa only [Fintype.prod_bool, Bool.false_eq_true, if_true, if_false, mul_comm] using he

theorem given_tower_refinement (μ : FiniteProb Ω) (Y : Ω → B) (F : Ω → C)
    (coarse : B → C) (hF : ∀ ω, F ω = coarse (Y ω)) (b : C)
    (hb : 0 < (μ.map F).weight b) (f : Ω → ℝ) :
    (μ.given F b).expect (fun ω => (μ.given Y (Y ω)).expect f) = (μ.given F b).expect f := by
  have he : F = fun ω => coarse (Y ω) := funext hF
  subst F
  exact μ.given_tower Y coarse b hb f

def kernelConflict (μ : FiniteProb Ω) (K L : Ω → FiniteProb (Option A))
    (G : Ω → A × A → Bool) : ℝ :=
  μ.expect (fun ω => ∑ a, ∑ b, (K ω).weight (some a)*(L ω).weight (some b)*bit (G ω (a,b)=true))

theorem kernelConflict_nonneg (μ : FiniteProb Ω) (K L : Ω → FiniteProb (Option A))
    (G : Ω → A × A → Bool) : 0 ≤ μ.kernelConflict K L G := by
  apply μ.expect_nonneg
  intro ω
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
    mul_nonneg (mul_nonneg ((K ω).nonneg _) ((L ω).nonneg _)) (bit_nonneg _)))

/-- Average product of the two shared-fiber endpoint probabilities equals
the conflict probability of the CURRENT projected kernels. Independence of
the original outputs is neither assumed nor needed. -/
theorem projected_shared_conflict (μ : FiniteProb Ω) (U V : Ω → Option A)
    (Y Z : Ω → B) (F : Ω → C) (fy fz : B → C)
    (hfy : ∀ ω, F ω = fy (Y ω)) (hfz : ∀ ω, F ω = fz (Z ω))
    (hind : ∀ b, 0 < (μ.map F).weight b →
      (μ.given F b).Independent (fun t : Bool => if t then Z else Y)) (G : C → A × A → Bool) :
    (μ.map F).expect (fun b =>
      (((μ.given F b).map U).product ((μ.given F b).map V)).prob
        (fun ab => selectedConflict (fun _ : Unit => fun a a' => G b (a,a')=true) ((),ab.1,ab.2))) =
      μ.kernelConflict (fun ω => (μ.given Y (Y ω)).map U)
        (fun ω => (μ.given Z (Z ω)).map V) (fun ω => G (F ω)) := by
  let H := fun ω => ∑ a, ∑ b, ((μ.given Y (Y ω)).map U).weight (some a) *
    ((μ.given Z (Z ω)).map V).weight (some b)*bit (G (F ω) (a,b)=true)
  have hpoint (c : C) (hc : 0 < (μ.map F).weight c) :
      (((μ.given F c).map U).product ((μ.given F c).map V)).prob
        (fun ab => selectedConflict (fun _ : Unit => fun a a' => G c (a,a')=true) ((),ab.1,ab.2)) =
      (μ.given F c).expect H := by
    rw [product_selected_probability]
    have he : (μ.given F c).expect H = (μ.given F c).expect (fun ω => ∑ a, ∑ b,
        ((μ.given Y (Y ω)).map U).weight (some a)*((μ.given Z (Z ω)).map V).weight (some b)*
          bit (G c (a,b)=true)) := by
      apply (μ.given F c).expect_congr_on_support
      intro ω hω
      dsimp [H]
      rw [μ.given_support_eq F c hc hω]
    rw [he, expect_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [expect_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hind' := (hind c hc).bool_product
      (fun y => ((μ.given Y y).map U).weight (some a))
      (fun z => ((μ.given Z z).map V).weight (some b))
    simp only [Bool.false_eq_true, if_false, if_true] at hind'
    have hu := μ.given_tower_refinement Y F fy hfy c hc (fun ω => bit (U ω=some a))
    have hv := μ.given_tower_refinement Z F fz hfz c hc (fun ω => bit (V ω=some b))
    change (μ.given F c).expect (fun ω => ((μ.given Y (Y ω)).map U).weight (some a)) =
      ((μ.given F c).map U).weight (some a) at hu
    change (μ.given F c).expect (fun ω => ((μ.given Z (Z ω)).map V).weight (some b)) =
      ((μ.given F c).map V).weight (some b) at hv
    rw [hu, hv] at hind'
    calc
      _ = bit (G c (a,b)=true) * (μ.given F c).expect (fun ω =>
          ((μ.given Y (Y ω)).map U).weight (some a)*((μ.given Z (Z ω)).map V).weight (some b)) := by
        rw [hind']; ring
      _ = _ := by
        rw [← expect_mul]
        apply (μ.given F c).expect_congr
        intro ω
        ring
  rw [(μ.map F).expect_congr_on_support _ _ hpoint]
  exact μ.total_conditional_expectation F H

theorem projected_endpoint_tails [DecidableEq A] (μ : FiniteProb Ω)
    (U V : Ω → Option A) (Y Z : Ω → B) (F : Ω → C) (fy fz : B → C)
    (hfy : ∀ ω, F ω = fy (Y ω)) (hfz : ∀ ω, F ω = fz (Z ω))
    (hind : ∀ b, 0 < (μ.map F).weight b →
      (μ.given F b).Independent (fun t : Bool => if t then Z else Y))
    (G : C → A × A → Bool) {ell : ℕ} (hell : 0 < ell) {q : ℝ}
    (hbad : μ.prob (fun ω => exceptionalMatrix ell (G (F ω))) ≤ q) :
    μ.expect (fun ω => ((μ.given F (F ω)).map U).tail ell*((μ.given F (F ω)).map V).tail ell) ≤
      4*μ.kernelConflict (fun ω => (μ.given Y (Y ω)).map U)
        (fun ω => (μ.given Z (Z ω)).map V) (fun ω => G (F ω))+q := by
  have h := (μ.map F).expect_mono (fun b =>
    matrix_tail_product ((μ.given F b).map U) ((μ.given F b).map V) (G b) hell)
  rw [expect_add, expect_mul, μ.projected_shared_conflict U V Y Z F fy fz hfy hfz hind G,
    expect_map] at h
  change _ ≤ 4*μ.kernelConflict _ _ _ + (μ.map F).prob (fun b => exceptionalMatrix ell (G b)) at h
  rw [prob_map] at h
  linarith

end FiniteProb
end
end MISLocal
