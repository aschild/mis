import MISLocal.HomogeneousEntropy
import MISLocal.ProjectionConflict

/-! Direct-projection conflict charging for a homogeneous local field with
short conditional support. The entropy inequality is derived, not assumed. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem geometric_projection_budget {I V E A : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Nonempty V] [Fintype E] [Fintype A]
    {T : I → Type*} [∀ i, Fintype (T i)] {d r : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d r)
    (U : V → (∀ i, T i) → Option A)
    (hlocal : ∀ v, ReadsOnly (U v) (g.readers v))
    (hhom : ViewHomogeneous (pi P) U g.vertexObservation g.sharedObservation g.left g.right)
    (j : ℕ) (hj : j ≤ r) (e₀ : E) (S : (∀ i, Option (T i)) → Finset A) {m : ℝ}
    (hm : 0 < m) (hcard : ∀ b, ((S b).card:ℝ) ≤ m)
    (hsupport : ∀ b, 0 < ((pi P).map (g.vertexObservation j (g.left e₀))).weight b → ∀ a,
      a ∉ S b → (((pi P).given (g.vertexObservation j (g.left e₀)) b).map (U (g.left e₀))).weight (some a)=0)
    (G : (∀ i, Option (T i)) → A × A → Bool)
    (hzero : (pi P).prob (fun ω => selectedConflict (fun b a a' => G b (a,a')=true)
      (g.sharedObservation j e₀ ω,U (g.left e₀) ω,U (g.right e₀) ω)) = 0) :
    (pi P).kernelConflict
      (fun ω => (((pi P).given (g.vertexObservation j (g.left e₀)) (g.vertexObservation j (g.left e₀) ω)).map (U (g.left e₀))))
      (fun ω => (((pi P).given (g.vertexObservation j (g.right e₀)) (g.vertexObservation j (g.right e₀) ω)).map (U (g.right e₀))))
      (fun ω => G (g.sharedObservation j e₀ ω)) ≤
        2*massBudget m ((pi P).prob (fun ω => U (g.left e₀) ω ≠ none))/((d:ℝ)+1) := by
  let μ := pi P
  let F := g.sharedObservation (T := T) j e₀
  let y := restrictObservation (T := T) (g.vertex j (g.left e₀))
  let z := restrictObservation (T := T) (g.vertex j (g.right e₀))
  have hy (ω : ∀ i, T i) : y (F ω) = g.vertexObservation j (g.left e₀) ω :=
    (g.vertex_from_shared j hj (g.left e₀) e₀ (Or.inl rfl) ω).symm
  have hz (ω : ∀ i, T i) : z (F ω) = g.vertexObservation j (g.right e₀) ω :=
    (g.vertex_from_shared j hj (g.right e₀) e₀ (Or.inr rfl) ω).symm
  have h := μ.direct_projection_rare_bound F (U (g.left e₀)) (U (g.right e₀)) y z S
    (selectedConflict (fun b a a' => G b (a,a')=true))
    (D := (d:ℝ)+1) (K := 0) (by positivity) hm (le_refl 0) hcard
    (by simpa only [hy] using hsupport)
    (by simpa only [hy, hz] using hhom.vertex_conditional_entropy j e₀ (g.right e₀) (g.endpoint_cover _))
    (by
      have he := homogeneous_conditional_entropy P g U hlocal hhom j hj e₀
      simpa only [hy, hz, add_sub_cancel_right, add_zero] using he)
    (by rwa [prob_map])
  rw [projectedPair_conflict_eq] at h
  simpa only [hy, hz] using h

end FiniteProb
end
end MISLocal
