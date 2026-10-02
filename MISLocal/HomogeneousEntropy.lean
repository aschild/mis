import MISLocal.InputGeometry

/-! The conditional entropy inequality for a homogeneous local output field,
derived from its independent sources and combinatorial routing geometry. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem homogeneous_conditional_entropy {I V E A : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Nonempty V] [Fintype E] [Fintype A]
    {T : I → Type*} [∀ i, Fintype (T i)] {d r : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d r)
    (U : V → (∀ i, T i) → Option A)
    (hlocal : ∀ v, ReadsOnly (U v) (g.readers v))
    (hhom : ViewHomogeneous (pi P) U g.vertexObservation g.sharedObservation g.left g.right)
    (j : ℕ) (hj : j ≤ r) (e₀ : E) :
    (((d:ℝ)+1)/2)*(pi P).condEntropy (fun ω => (U (g.left e₀) ω,U (g.right e₀) ω))
      (g.sharedObservation j e₀) ≥
        (d:ℝ)*(pi P).condEntropy (U (g.left e₀)) (g.vertexObservation j (g.left e₀)) := by
  exact symmetric_conditional_entropy_finite P U g.left g.right g.readers (g.vertex j) (g.shared j)
    hlocal (g.charge j hj) g.edgeCount
    (fun v => hhom.vertex_conditional_entropy j e₀ v (g.endpoint_cover v))
    (fun e => hhom.edge_conditional_entropy j e₀ e)

theorem keptOutput_readsOnly {I A B : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A] [Fintype B]
    (μ : FiniteProb (∀ i, T i)) (U : (∀ i, T i) → Option A) (Y : (∀ i, T i) → B)
    (m : ℕ) (R : Finset I) (hU : ReadsOnly U R) (hY : ReadsOnly Y R) :
    ReadsOnly (μ.keptOutput U Y m) R := by
  intro x z hxz
  simp only [keptOutput, hU x z hxz, hY x z hxz]

theorem deletedOutput_readsOnly {I A B : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A] [Fintype B]
    (μ : FiniteProb (∀ i, T i)) (U : (∀ i, T i) → Option A) (Y : (∀ i, T i) → B)
    (m : ℕ) (R : Finset I) (hU : ReadsOnly U R) (hY : ReadsOnly Y R) :
    ReadsOnly (μ.deletedOutput U Y m) R := by
  intro x z hxz
  simp only [deletedOutput, hU x z hxz, hY x z hxz]

theorem survivor_readsOnly {I A B : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A] [Fintype B]
    (μ : FiniteProb (∀ i, T i)) (U : (∀ i, T i) → Option A) (Y : ℕ → (∀ i, T i) → B)
    (m n : ℕ) (R : Finset I) (hU : ReadsOnly U R) (hY : ∀ j, j < n → ReadsOnly (Y j) R) :
    ReadsOnly (μ.survivor U Y m n) R := by
  induction n with
  | zero => exact hU
  | succ n ih =>
    exact μ.keptOutput_readsOnly _ _ m R (ih (fun j hj => hY j (by omega))) (hY n (by omega))

theorem firstDeleted_readsOnly {I A B : Type*} [Fintype I] [DecidableEq I]
    {T : I → Type*} [∀ i, Fintype (T i)] [Fintype A] [Fintype B]
    (μ : FiniteProb (∀ i, T i)) (U : (∀ i, T i) → Option A) (Y : ℕ → (∀ i, T i) → B)
    (m n : ℕ) (R : Finset I) (hU : ReadsOnly U R) (hY : ∀ j, j ≤ n → ReadsOnly (Y j) R) :
    ReadsOnly (μ.firstDeleted U Y m n) R :=
  μ.deletedOutput_readsOnly _ _ m R
    (μ.survivor_readsOnly U Y m n R hU (fun j hj => hY j hj.le)) (hY n (le_refl n))

end FiniteProb
end
end MISLocal
