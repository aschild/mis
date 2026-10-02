import MISLocal.NestedGiven

/-! A finite stochastic rule is realized by a private table, independently
sampled at every vertex. Tables are indexed by the LOCAL view, not the entire
input configuration; this distinction preserves pointwise locality. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C I : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
  [Fintype I] [DecidableEq I] [DecidableEq B]

theorem pi_expect_two {T : I → Type*} [∀ i, Fintype (T i)]
    (P : ∀ i, FiniteProb (T i)) (i j : I) (hji : j ≠ i)
    (f : T i → ℝ) (g : T j → ℝ) :
    (pi P).expect (fun x => f (x i)*g (x j)) = (P i).expect f * (P j).expect g := by
  have he := (pi P).expect_map (Equiv.piSplitAt i T)
    (fun ab => f ab.1*g (ab.2 ⟨j,hji⟩))
  rw [pi_splitAt, product_expect] at he
  simp only [expect_mul, pi_expect_coordinate, Equiv.piSplitAt_apply] at he
  rw [← he]
  simp only [expect, ← mul_assoc, ← Finset.sum_mul]

def tableProbability (K : I → B → FiniteProb A) : FiniteProb (I → B → A) :=
  pi (fun i => pi (K i))

def tableDraw (Y : I → Ω → B) (i : I) (x : Ω × (I → B → A)) : A := x.2 i (Y i x.1)

theorem table_expect_one (K : I → B → FiniteProb A) (i : I) (b : B) (f : A → ℝ) :
    (tableProbability K).expect (fun t => f (t i b)) = (K i b).expect f := by
  exact (pi_expect_coordinate (fun i => pi (K i)) i (fun t => f (t b))).trans
    (pi_expect_coordinate (K i) b f)

theorem table_expect_pair (K : I → B → FiniteProb A) (i j : I) (hji : j ≠ i)
    (b c : B) (f g : A → ℝ) :
    (tableProbability K).expect (fun t => f (t i b)*g (t j c)) =
      (K i b).expect f * (K j c).expect g := by
  rw [tableProbability, pi_expect_two (fun i => pi (K i)) i j hji
    (fun t => f (t b)) (fun t => g (t c))]
  rw [pi_expect_coordinate, pi_expect_coordinate]

theorem table_pair_distribution (K : I → B → FiniteProb A) (i j : I) (hji : j ≠ i)
    (b c : B) :
    (tableProbability K).map (fun t => (t i b,t j c)) = (K i b).product (K j c) := by
  ext ab
  change (tableProbability K).expect (fun t => bit ((t i b,t j c) = ab)) = _
  have he (t : I → B → A) : bit ((t i b,t j c) = ab) =
      bit (t i b = ab.1)*bit (t j c = ab.2) := by
    by_cases h0 : t i b = ab.1 <;> by_cases h1 : t j c = ab.2 <;>
      simp [bit, Prod.ext_iff, h0, h1]
  rw [(tableProbability K).expect_congr he,
    table_expect_pair K i j hji b c (fun x => bit (x = ab.1)) (fun x => bit (x = ab.2))]
  simp [expect, bit, product]

omit [DecidableEq B] in
theorem product_map_left (P : FiniteProb Ω) (Q : FiniteProb A) (Y : Ω → B) :
    (P.product Q).map (fun x => Y x.1) = P.map Y := by
  rw [← map_comp _ Prod.fst Y, product_map_fst]

omit [DecidableEq B] in
theorem product_given_left (P : FiniteProb Ω) (Q : FiniteProb A) (Y : Ω → B)
    (b : B) (hb : 0 < (P.map Y).weight b) :
    (P.product Q).given (fun x => Y x.1) b = (P.given Y b).product Q := by
  have hb' : 0 < ((P.product Q).map (fun x => Y x.1)).weight b := by
    rwa [product_map_left]
  ext x
  rw [given_weight _ _ b hb', product_map_left]
  change (P.weight x.1*Q.weight x.2)*bit (Y x.1=b)/(P.map Y).weight b =
    (P.given Y b).weight x.1*Q.weight x.2
  rw [P.given_weight Y b hb]
  ring

/-- Sampling the original output's conditional distribution reproduces
that distribution exactly on every positive local-view fiber. -/
theorem sampled_conditional_output (μ : FiniteProb Ω) (U : I → Ω → A) (Y : I → Ω → B)
    (i : I) (b : B) (hb : 0 < (μ.map (Y i)).weight b) :
    let K := fun i b => (μ.given (Y i) b).map (U i)
    ((μ.product (tableProbability K)).given (fun x => Y i x.1) b).map (tableDraw Y i) = K i b := by
  dsimp only
  rw [product_given_left μ _ (Y i) b hb]
  ext a
  change ((μ.given (Y i) b).product _).expect (fun x => bit (tableDraw Y i x = a)) = _
  rw [product_expect]
  simp only [tableDraw]
  simp_rw [table_expect_one _ i _ (fun x => bit (x = a))]
  calc
    _ = (μ.given (Y i) b).expect (fun _ => ((μ.given (Y i) b).map (U i)).weight a) := by
      apply (μ.given (Y i) b).expect_congr_on_support
      intro ω hω
      dsimp only
      rw [μ.given_support_eq (Y i) b hb hω]
      simp [expect, bit]
    _ = _ := expect_const _ _

end FiniteProb
end
end MISLocal
