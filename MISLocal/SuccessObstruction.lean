import MISLocal.Obstruction
/-! Averaging only needs success on a legal realization to force repaired occupancy. -/
open MeasureTheory
namespace MISLocal
noncomputable section
theorem success_obstruction {Ω W : Type*} [Fintype Ω] [MeasurableSpace W]
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (unique bad : Ω → Prop) (success occupied : Ω → W → Prop)
    (ε δ γ β : ℝ) (hε : ε ≤ 1)
    (hcollision : μ.prob (fun g => ¬unique g) ≤ δ) (hbad : μ.prob bad ≤ γ)
    (hcorrect : ∀ g, 1-ε ≤ ν.real {w | success g w})
    (hforce : ∀ g, unique g → ¬bad g → ∀ w, success g w → occupied g w)
    (hmeas : ∀ g, MeasurableSet {w | occupied g w})
    (hfixed : ∀ w, μ.prob (fun g => occupied g w) ≤ β) : (1-ε)*(1-δ-γ) ≤ β := by
  classical
  let good := fun g => unique g ∧ ¬bad g
  have hlower : 1-δ-γ ≤ μ.prob good := by
    have hi := μ.prob_and_lower unique (fun g => ¬bad g)
    rw [μ.prob_not] at hi
    have hu := μ.prob_not unique
    dsimp only [good]
    linarith
  have hpoint : ∀ g, (1-ε)*bit (good g) ≤ ν.real {w | occupied g w} := by
    intro g
    by_cases hg : good g
    · have hs : {w | success g w} ⊆ {w | occupied g w} := hforce g hg.1 hg.2
      simpa [bit,hg] using (hcorrect g).trans (measureReal_mono hs)
    · simp [bit,hg,measureReal_nonneg]
  have hmean := μ.expect_mono hpoint
  rw [μ.expect_mul] at hmean
  have hupper := average_fixed_tape_bound μ ν (fun g => {w | occupied g w}) hmeas β hfixed
  exact (mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hε)).trans (hmean.trans hupper)
end
end MISLocal
