import MISLocal.FiniteProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fixing a possibly infinite tape table, then averaging

The graph sample type is finite. The tape-table space is an arbitrary measurable
probability space: in particular, this theorem does not silently replace infinite
random tapes by finite random seeds. Measurability of the occupancy events is
explicit. No independence between graph-derived IDs and the graph is postulated.
-/

open scoped BigOperators
open MeasureTheory

namespace MISLocal
noncomputable section

theorem average_fixed_tape_bound
    {Ω W : Type*} [Fintype Ω] [MeasurableSpace W]
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (B : Ω → Set W) (hB : ∀ g, MeasurableSet (B g)) (β : ℝ)
    (hfixed : ∀ w, μ.prob (fun g => w ∈ B g) ≤ β) :
    μ.expect (fun g => ν.real (B g)) ≤ β := by
  classical
  have hI (g : Ω) : Integrable (fun w => bit (w ∈ B g)) ν := by
    simpa [bit, Set.indicator] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : W => (1 : ℝ)) ν).indicator (hB g)
  have hval (g : Ω) : (∫ w, bit (w ∈ B g) ∂ν) = ν.real (B g) := by
    simpa [bit, Set.indicator] using
      (integral_indicator_const (μ := ν) (1 : ℝ) (hB g))
  have hi : Integrable (fun w => μ.prob (fun g => w ∈ B g)) ν := by
    exact integrable_finset_sum _ (fun g _ => (hI g).const_mul (μ.weight g))
  have heq : (∫ w, μ.prob (fun g => w ∈ B g) ∂ν) =
      μ.expect (fun g => ν.real (B g)) := by
    unfold FiniteProb.prob FiniteProb.expect
    rw [integral_finset_sum _ (fun g _ => (hI g).const_mul (μ.weight g))]
    simp only [integral_const_mul, hval]
  rw [← heq]
  calc
    _ ≤ ∫ _ : W, β ∂ν := integral_mono hi (integrable_const β) hfixed
    _ = β := by simp

end
end MISLocal
