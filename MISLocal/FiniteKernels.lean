import MISLocal.TableSampling
import MISLocal.SymmetryTransport

/-! Finite probability kernels, their private-table realization, and exact
averaging identities. Kernel weights may be arbitrary real probabilities. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

variable {Ω A B C V : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C] [Fintype V]

def bind (μ : FiniteProb Ω) (K : Ω → FiniteProb A) : FiniteProb A where
  weight a := μ.expect (fun ω => (K ω).weight a)
  nonneg a := μ.expect_nonneg (fun ω => (K ω).nonneg a)
  total := by
    rw [← expect_sum]
    simp only [FiniteProb.total, expect_const]

theorem expect_bind (μ : FiniteProb Ω) (K : Ω → FiniteProb A) (f : A → ℝ) :
    (μ.bind K).expect f = μ.expect (fun ω => (K ω).expect f) := by
  simp only [bind, expect, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext ω
  congr 1
  funext a
  ring

theorem bind_map (μ : FiniteProb Ω) (K : Ω → FiniteProb A) (f : A → B) :
    (μ.bind K).map f = μ.bind (fun ω => (K ω).map f) := by
  ext b
  exact μ.expect_bind K (fun a => bit (f a=b))

theorem product_map_bind (μ : FiniteProb Ω) (Q : FiniteProb A) (X : Ω × A → B) :
    (μ.product Q).map X = μ.bind (fun ω => Q.map (fun a => X (ω,a))) := by
  ext b
  exact product_expect μ Q (fun x => bit (X x=b))

theorem bind_transport (μ : FiniteProb Ω) (e : Ω → Ω) (he : μ.map e = μ)
    (K K' : Ω → FiniteProb A) (α : A ≃ A)
    (hK : ∀ ω, K' (e ω) = (K ω).map α) : μ.bind K' = (μ.bind K).map α := by
  rw [bind_map]
  ext a
  change μ.expect (fun ω => (K' ω).weight a) = μ.expect (fun ω => ((K ω).map α).weight a)
  rw [← μ.expect_invariant e he (fun ω => (K' ω).weight a)]
  exact μ.expect_congr (fun ω => congrArg (fun P => P.weight a) (hK ω))

def mixedPair (μ : FiniteProb Ω) (F : Ω → C) (K L : Ω → FiniteProb A) :
    FiniteProb (C × A × A) :=
  μ.bind (fun ω => ((K ω).product (L ω)).map (fun ab => (F ω,ab.1,ab.2)))

theorem table_mixedPair [DecidableEq V] [DecidableEq B]
    (μ : FiniteProb Ω) (Y : V → Ω → B) (K : V → B → FiniteProb A)
    (i j : V) (hji : j ≠ i) (F : Ω → C) :
    (μ.product (tableProbability K)).map (fun x => (F x.1,tableDraw Y i x,tableDraw Y j x)) =
      μ.mixedPair F (fun ω => K i (Y i ω)) (fun ω => K j (Y j ω)) := by
  rw [product_map_bind]
  congr 1
  funext ω
  change (tableProbability K).map (fun t => (F ω,t i (Y i ω),t j (Y j ω))) = _
  rw [← map_comp (tableProbability K) (fun t => (t i (Y i ω),t j (Y j ω)))
      (fun ab : A × A => (F ω,ab.1,ab.2)),
    table_pair_distribution K i j hji]

theorem mixedPair_weight (μ : FiniteProb Ω) (F : Ω → C) (K L : Ω → FiniteProb A)
    (c : C) (a b : A) :
    (μ.mixedPair F K L).weight (c,a,b) =
      μ.expect (fun ω => bit (F ω=c)*(K ω).weight a*(L ω).weight b) := by
  apply μ.expect_congr
  intro ω
  change ((K ω).product (L ω)).prob (fun ab => (F ω,ab.1,ab.2) = (c,a,b)) = _
  by_cases hf : F ω=c
  · simp [prob, expect, product, Fintype.sum_prod_type, bit, hf]
  · simp [prob, expect, product, Fintype.sum_prod_type, bit, hf]

/-- If the shared observation contains the endpoint views, the independently
sampled pair has exactly the direct-projection distribution used in the KL
budget. No equality of realized original and sampled outputs is claimed. -/
theorem sampled_is_projectedPair [DecidableEq V] [DecidableEq B]
    (μ : FiniteProb Ω) (U : V → Ω → A) (Y : V → Ω → B)
    (i j : V) (hji : j ≠ i) (F : Ω → C) (yi yj : C → B)
    (hi : ∀ ω, Y i ω = yi (F ω)) (hj : ∀ ω, Y j ω = yj (F ω)) :
    let K := fun v b => (μ.given (Y v) b).map (U v)
    (μ.product (tableProbability K)).map (fun x => (F x.1,tableDraw Y i x,tableDraw Y j x)) =
      μ.projectedPair F (U i) (U j) yi yj := by
  dsimp only
  rw [table_mixedPair μ Y _ i j hji F]
  have hYi : Y i = fun ω => yi (F ω) := funext hi
  have hYj : Y j = fun ω => yj (F ω) := funext hj
  ext t
  rcases t with ⟨c,a,b⟩
  rw [mixedPair_weight]
  have hpoint (ω : Ω) : bit (F ω=c)*((μ.given (Y i) (Y i ω)).map (U i)).weight a *
      ((μ.given (Y j) (Y j ω)).map (U j)).weight b =
      (((μ.given (Y i) (yi c)).map (U i)).weight a *
        ((μ.given (Y j) (yj c)).map (U j)).weight b)*bit (F ω=c) := by
    by_cases hf : F ω=c
    · rw [hi ω, hj ω, hf]
      ring
    · simp [bit, hf]
  rw [μ.expect_congr hpoint, expect_mul]
  simp only [hYi, hYj, projectedPair, prob, map]
  ring

end FiniteProb
end
end MISLocal
