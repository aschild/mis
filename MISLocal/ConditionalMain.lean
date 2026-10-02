import MISLocal.Obstruction
import MISLocal.Numerics

/-!
# A checked conditional implication, NOT the full LOCAL lower bound

This combines the verified graph/probability reduction with the verified
numerical estimates. Its parameters display the remaining mathematical work:
the concrete construction must establish `hcollision`, `hdomination`,
`hsimulation`, `hfixed`, the size/degree estimates, and event measurability.
This is the legacy conditional wrapper. `GraphTapeReduction.lean` supplies a
new finite obstruction deriving the occupancy premise from the proved
`graph_occupancy` theorem, while keeping the other model obligations explicit.
-/

open MeasureTheory

namespace MISLocal
noncomputable section

theorem conditional_round_lower_bound
    {Ω W V : Type*} [Fintype Ω] [Fintype V] [MeasurableSpace W]
    (μ : FiniteProb Ω) (ν : Measure W) [IsProbabilityMeasure ν]
    (G : Ω → SimpleGraph V) (C : Set V)
    (output candidates : Ω → W → Set V) (uniqueIDs : Ω → Prop)
    (T : ℕ) (D ε δ γ : ℝ)
    (hD : 1 < D) (hDlower : Real.log (Fintype.card V : ℝ) / 5 ≤ D)
    (hDupper : D ≤ Real.log (Fintype.card V : ℝ))
    (hlarge : 3 ≤ Real.log (Fintype.card V : ℝ) /
      (100000 * Real.log (Real.log (Fintype.card V : ℝ))))
    (hε : ε ≤ 1 / 3) (herrors : δ + γ ≤ 1 / 4)
    (hcollision : μ.prob (fun g => ¬uniqueIDs g) ≤ δ)
    (hdomination : μ.prob (fun g => ExternallyDominatable (G g) C) ≤ γ)
    (hcorrect : ∀ g,
      1 - ε ≤ ν.real {w | Maximal (G g).IsIndepSet (output g w)})
    (hsimulation : ∀ g, uniqueIDs g → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (G g).Adj v x → (x ∈ candidates g w ↔ x ∈ output g w))
    (hmeas : ∀ g, MeasurableSet {w | Occupies C (repair (G g) (candidates g w))})
    (hfixed : ∀ w,
      μ.prob (fun g => Occupies C (repair (G g) (candidates g w))) ≤
        occupancyCap (T + 3) D) :
    Real.log (Fintype.card V : ℝ) /
      (100000 * Real.log (Real.log (Fintype.card V : ℝ))) ≤ (T : ℝ) := by
  apply size_round_lower_bound hD hDlower hDupper hlarge hε herrors
  exact finite_obstruction μ ν G C output candidates uniqueIDs ε δ γ
    (occupancyCap (T + 3) D) (by linarith) hcollision hdomination hcorrect
    hsimulation hmeas hfixed

end
end MISLocal
