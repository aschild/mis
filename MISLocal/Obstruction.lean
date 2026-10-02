import MISLocal.Repair
import MISLocal.TapeAveraging

/-!
# The generic finite obstruction

This module proves the probability-transfer argument. `hsimulation` is a
hypothesis saying that a supplied candidate process matches the real algorithm
on the closed neighborhood of C when local IDs are unique. Deriving this from
LOCAL transition rules is done in the concrete reduction modules. Here
`hfixed` is a per-fixed-table bound. The anonymous occupancy and concrete
reduction modules discharge it for the supplied uniform program.

These hypotheses are parameters of the theorem, never new axioms or hidden
fields of a definition of "LOCAL algorithm".
-/

open MeasureTheory

namespace MISLocal
noncomputable section

variable {Ω W V : Type*} [Fintype Ω] [MeasurableSpace W]

/-- Transfer of occupancy, with the same explicit simulation interface. -/
theorem occupancy_transfer
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (G : Ω → SimpleGraph V) (C : Set V)
    (output candidates : Ω → W → Set V) (uniqueIDs : Ω → Prop)
    (ε δ β : ℝ) (hε : 0 ≤ ε)
    (hcollision : μ.prob (fun g => ¬uniqueIDs g) ≤ δ)
    (hcorrect : ∀ g, ν.real {w | ¬(G g).IsIndepSet (output g w)} ≤ ε)
    (hsimulation : ∀ g, uniqueIDs g → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (G g).Adj v x → (x ∈ candidates g w ↔ x ∈ output g w))
    (hmeas : ∀ g, MeasurableSet {w | Occupies C (repair (G g) (candidates g w))})
    (hfixed : ∀ w,
      μ.prob (fun g => Occupies C (repair (G g) (candidates g w))) ≤ β) :
    μ.expect (fun g => ν.real {w | Occupies C (output g w)}) ≤ β + ε + δ := by
  classical
  let B : Ω → Set W := fun g => {w | Occupies C (repair (G g) (candidates g w))}
  have hpoint (g : Ω) : ν.real {w | Occupies C (output g w)} ≤
      ν.real (B g) + ε + bit (¬uniqueIDs g) := by
    by_cases hu : uniqueIDs g
    · have hsub : {w | Occupies C (output g w)} ⊆
          B g ∪ {w | ¬(G g).IsIndepSet (output g w)} := by
        intro w hw
        by_cases hi : (G g).IsIndepSet (output g w)
        · exact Or.inl ((repair_occupancy_agrees (G g) hi
            (hsimulation g hu w)).mpr hw)
        · exact Or.inr hi
      have hbound := (measureReal_mono (μ := ν) hsub).trans
        (measureReal_union_le (B g) {w | ¬(G g).IsIndepSet (output g w)})
      have hc := hcorrect g
      simp only [bit, not_true_eq_false, hu, if_false, add_zero]
      linarith
    · have hnonneg : 0 ≤ ν.real (B g) := measureReal_nonneg
      have hupper : ν.real {w | Occupies C (output g w)} ≤ 1 := measureReal_le_one
      simp only [bit, if_pos hu]
      linarith
  have hmean := μ.expect_mono hpoint
  rw [μ.expect_add, μ.expect_add, μ.expect_const] at hmean
  have hupper : μ.expect (fun g => ν.real (B g)) ≤ β :=
    average_fixed_tape_bound μ ν B hmeas β hfixed
  change μ.expect (fun g => ν.real {w | Occupies C (output g w)}) ≤
    μ.expect (fun g => ν.real (B g)) + ε + μ.prob (fun g => ¬uniqueIDs g) at hmean
  linarith

/-- Necessary quantitative condition, allowing arbitrarily long random tapes. -/
theorem finite_obstruction
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (G : Ω → SimpleGraph V) (C : Set V)
    (output candidates : Ω → W → Set V) (uniqueIDs : Ω → Prop)
    (ε δ γ β : ℝ) (hε : ε ≤ 1)
    (hcollision : μ.prob (fun g => ¬uniqueIDs g) ≤ δ)
    (hdomination : μ.prob (fun g => ExternallyDominatable (G g) C) ≤ γ)
    (hcorrect : ∀ g,
      1 - ε ≤ ν.real {w | Maximal (G g).IsIndepSet (output g w)})
    (hsimulation : ∀ g, uniqueIDs g → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (G g).Adj v x → (x ∈ candidates g w ↔ x ∈ output g w))
    (hmeas : ∀ g, MeasurableSet {w | Occupies C (repair (G g) (candidates g w))})
    (hfixed : ∀ w,
      μ.prob (fun g => Occupies C (repair (G g) (candidates g w))) ≤ β) :
    (1 - ε) * (1 - δ - γ) ≤ β := by
  classical
  let good : Ω → Prop := fun g => uniqueIDs g ∧ ¬ExternallyDominatable (G g) C
  let B : Ω → Set W := fun g => {w | Occupies C (repair (G g) (candidates g w))}
  have hlower : 1 - δ - γ ≤ μ.prob good := by
    have hi := μ.prob_and_lower uniqueIDs
      (fun g => ¬ExternallyDominatable (G g) C)
    rw [μ.prob_not] at hi
    have hu := μ.prob_not uniqueIDs
    dsimp [good]
    linarith
  have hpoint : ∀ g, (1 - ε) * bit (good g) ≤ ν.real (B g) := by
    intro g
    by_cases hg : good g
    · have hsub : {w | Maximal (G g).IsIndepSet (output g w)} ⊆ B g := by
        intro w hw
        have hoc : Occupies C (output g w) :=
          maximal_occupies_of_not_externally_dominatable (G g) hg.2 hw
        exact (repair_occupancy_agrees (G g) hw.1
          (hsimulation g hg.1 w)).mpr hoc
      simpa [bit, hg] using (hcorrect g).trans (measureReal_mono hsub)
    · simp [bit, hg, measureReal_nonneg]
  have hmean := μ.expect_mono hpoint
  rw [μ.expect_mul] at hmean
  have hupper : μ.expect (fun g => ν.real (B g)) ≤ β :=
    average_fixed_tape_bound μ ν B hmeas β hfixed
  calc
    (1 - ε) * (1 - δ - γ) ≤ (1 - ε) * μ.prob good :=
      mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hε)
    _ ≤ μ.expect (fun g => ν.real (B g)) := hmean
    _ ≤ β := hupper

end
end MISLocal
