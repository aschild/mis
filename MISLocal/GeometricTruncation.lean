import MISLocal.InputGeometry
import MISLocal.ProjectedTails
import MISLocal.LocalScalarMoment
import MISLocal.TruncationEstimate

/-! The robust truncation estimate on an explicit independent-source
geometry. The scalar, branch and tail estimates are all derived here; none
is assumed as a probability-inequality premise. -/

open scoped BigOperators Classical

namespace MISLocal
noncomputable section
namespace FiniteProb

theorem geometric_truncation {I V E A : Type}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]
    {T : I → Type} [∀ i, Fintype (T i)] {d r : ℕ}
    (P : ∀ i, FiniteProb (T i)) (g : ProductInputGeometry I V E d r)
    (U : V → (∀ i, T i) → Option A)
    (hhom : ViewHomogeneous (pi P) U g.vertexObservation g.sharedObservation g.left g.right)
    (j : ℕ) (hj : j < r) (e₀ : E) (ell M m : ℕ)
    (hD : 12 ≤ (d:ℝ)+1) (hlog : 1 ≤ Real.log ((d:ℝ)+1))
    (hell : 0 < ell) (hM : 0 < M) (hm : 0 < m) (hellM : 32*ell ≤ M)
    (hsize : (M:ℝ)*((d:ℝ)+1) ≤ ((d:ℝ)+1)^4)
    (hratio : (M:ℝ)/m = 1/((d:ℝ)+1))
    (hatom : ∀ v b, 0 < ((pi P).map (g.vertexObservation (j+1) v)).weight b → ∀ a,
      (((pi P).given (g.vertexObservation (j+1) v) b).map (U v)).weight (some a) ≤ 1/(m:ℝ))
    (G : (∀ i, Option (T i)) → A × A → Bool) {q : ℝ}
    (hbad : (pi P).prob (fun ω => exceptionalMatrix ell (G (g.sharedObservation (j+1) e₀ ω))) ≤ q)
    (hq : q ≤ 1/((d:ℝ)+1)^2) :
    (pi P).prob (fun ω => U (g.left e₀) ω ≠ none) ≤
      2100*Real.log ((d:ℝ)+1)/((d:ℝ)+1) +
        6*Real.sqrt ((pi P).kernelConflict
          (fun ω => ((pi P).given (g.vertexObservation j (g.left e₀)) (g.vertexObservation j (g.left e₀) ω)).map (U (g.left e₀)))
          (fun ω => ((pi P).given (g.vertexObservation j (g.right e₀)) (g.vertexObservation j (g.right e₀) ω)).map (U (g.right e₀)))
          (fun ω => G (g.sharedObservation (j+1) e₀ ω))) := by
  let μ := pi P
  let D : ℝ := (d:ℝ)+1
  let W := g.vertexObservation (T := T)
  let F := g.sharedObservation (T := T)
  let f := fun v => μ.occupancyScalar (U v) (W (j+1) v) D
  let p := μ.expect (fun ω => f (g.left e₀) (W (j+1) (g.left e₀) ω))
  have hDp : 0 < D := by dsimp [D]; positivity
  have hmean (v : V) : μ.expect (fun ω => f v (W (j+1) v ω)) = p :=
    hhom.scalar_mean (j+1) D e₀ v (g.endpoint_cover v)
  have hscalar := scalar_overlap_from_sources P (W (j+1)) f
    (fun v b => μ.occupancyScalar_nonneg (U v) (W (j+1) v) D b)
    (fun v b => μ.occupancyScalar_le_one (U v) (W (j+1) v) hDp b)
    g.left g.right g.readers
    (fun v => observeInputs_readsOnly _ _ (g.vertex_readers (j+1) v (by omega)))
    g.unconditionedCharge g.degree g.edgeCount g.noLoop e₀ hmean
    (fun e => hhom.scalar_pair_moment (j+1) D e₀ e)
  have hfailure (v : V) (hve : edgeIncident g.left g.right v e₀) :
      μ.expect (fun ω => f v (W (j+1) v ω) *
        bit (((μ.given (F (j+1) e₀) (F (j+1) e₀ ω)).map (U v)).tail ell < f v (W (j+1) v ω))) ≤
          (256*Real.log D/D)*p := by
    have hc : Fintype.card {e // edgeIncident g.left g.right v e} = d+1 := by
      rw [Fintype.card_subtype, g.degree]
    have href (e : {e // edgeIncident g.left g.right v e}) (ω : ∀ i, T i) :
        W (j+1) v ω = restrictObservation (g.vertex (j+1) v) (F (j+1) e.val ω) :=
      g.vertex_from_shared (j+1) (by omega) v e.val e.property ω
    have hh := μ.weighted_branch_at (U v) (W (j+1) v)
      (fun e : {e // edgeIncident g.left g.right v e} => F (j+1) e.val)
      (fun _ => restrictObservation (g.vertex (j+1) v)) href ell M m
      (by simpa only [hc, Nat.cast_add, Nat.cast_one] using hD)
      (by simpa only [hc, Nat.cast_add, Nat.cast_one] using hlog) hM hm hellM
      (by simpa only [hc, Nat.cast_add, Nat.cast_one] using hsize)
      (by simpa only [hc, Nat.cast_add, Nat.cast_one] using hratio)
      (g.branch_views_independent P (j+1) (by omega) v) (hatom v) ⟨e₀,hve⟩
      (fun e => by
        simpa only [hc, Nat.cast_add, Nat.cast_one] using
          hhom.weighted_failure_equal (j+1) D ell v e₀ e.val hve e.property)
    have hh' : μ.expect (fun ω => f v (W (j+1) v ω) *
        bit (((μ.given (F (j+1) e₀) (F (j+1) e₀ ω)).map (U v)).tail ell < f v (W (j+1) v ω))) ≤
          (256*Real.log D/D)*μ.expect (fun ω => f v (W (j+1) v ω)) := by
      simpa only [hc, Nat.cast_add, Nat.cast_one] using hh
    rwa [hmean] at hh'
  have htail := μ.projected_endpoint_tails (U (g.left e₀)) (U (g.right e₀))
    (W j (g.left e₀)) (W j (g.right e₀)) (F (j+1) e₀)
    (restrictObservation (g.shared (j+1) e₀)) (restrictObservation (g.shared (j+1) e₀))
    (g.next_shared_from_vertex j hj (g.left e₀) e₀ (Or.inl rfl))
    (g.next_shared_from_vertex j hj (g.right e₀) e₀ (Or.inr rfl))
    (g.endpoint_views_independent P j hj e₀) G hell hbad
  exact μ.truncation_from_local_moments (U (g.left e₀)) (W (j+1) (g.left e₀))
    (fun ω => f (g.right e₀) (W (j+1) (g.right e₀) ω))
    (fun ω => ((μ.given (F (j+1) e₀) (F (j+1) e₀ ω)).map (U (g.left e₀))).tail ell)
    (fun ω => ((μ.given (F (j+1) e₀) (F (j+1) e₀ ω)).map (U (g.right e₀))).tail ell)
    hDp hlog (μ.kernelConflict_nonneg _ _ _) hq
    (fun ω => μ.occupancyScalar_nonneg _ _ _ _)
    (fun ω => μ.occupancyScalar_le_one _ _ hDp _)
    (fun ω => listTail_nonneg _ _) (fun ω => listTail_nonneg _ _) htail
    (hfailure (g.left e₀) (Or.inl rfl)) (hfailure (g.right e₀) (Or.inr rfl)) hscalar

end FiniteProb
end
end MISLocal
