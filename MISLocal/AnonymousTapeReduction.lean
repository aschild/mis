import MISLocal.AnonymousOccupancy
import MISLocal.GraphTapeReduction

/-! The fixed-tape averaging and finite obstruction with anonymous rules.
Their interfaces no longer require a view-symmetry or locality premise.
The concrete LOCAL simulation and its error estimates remain separate work. -/

open MeasureTheory
namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V W : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [MeasurableSpace W]
    {d n k : ℕ} {Q : Type} [Fintype Q]

theorem averaged_anonymous_graph_occupancy
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    (R : FiniteProb Q) (ν : Measure W) [IsProbabilityMeasure ν]
    (A : W → AnonymousRule V G.edgeSet k Q) (e₀ : G.edgeSet)
    (hzero : ∀ w, (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω,
          runAnonymous G (A w) (n+1) (edgeRight G e₀) ω)) = 0)
    (hmeas : ∀ ω, MeasurableSet {w | runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω ≠ none})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).expect
      (fun ω => ν.real {w | runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω ≠ none}) ≤
        occupancyCap (n+1) ((d+1:ℕ):ℝ) :=
  average_fixed_tape_bound _ ν _ hmeas _ (fun w =>
    anonymous_graph_occupancy G hreg ht R (A w) e₀ (hzero w) hD hk hlower hupper)

theorem anonymous_graph_finite_obstruction {X : Type*}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    (R : FiniteProb Q) (ν : Measure W) [IsProbabilityMeasure ν]
    (H : (∀ i, matrixPrivateType G k (fun _ => Q) i) → SimpleGraph X) (C : Set X)
    (output candidates : (∀ i, matrixPrivateType G k (fun _ => Q) i) → W → Set X)
    (uniqueIDs : (∀ i, matrixPrivateType G k (fun _ => Q) i) → Prop)
    (A : W → AnonymousRule V G.edgeSet k Q) (e₀ : G.edgeSet)
    (hzero : ∀ w, (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω,
          runAnonymous G (A w) (n+1) (edgeRight G e₀) ω)) = 0)
    (hrep : ∀ ω w, Occupies C (repair (H ω) (candidates ω w)) ↔
      runAnonymous G (A w) (n+1) (edgeLeft G e₀) ω ≠ none)
    (ε δ γ : ℝ) (hε : ε ≤ 1)
    (hcollision : (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob
      (fun ω => ¬uniqueIDs ω) ≤ δ)
    (hdomination : (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))).prob
      (fun ω => ExternallyDominatable (H ω) C) ≤ γ)
    (hcorrect : ∀ ω, 1-ε ≤ ν.real {w | Maximal (H ω).IsIndepSet (output ω w)})
    (hsimulation : ∀ ω, uniqueIDs ω → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (H ω).Adj v x → (x ∈ candidates ω w ↔ x ∈ output ω w))
    (hmeas : ∀ ω, MeasurableSet {w | Occupies C (repair (H ω) (candidates ω w))})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (1-ε)*(1-δ-γ) ≤ occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  apply finite_obstruction (FiniteProb.pi (matrixPrivateProbability G k (fun _ => R))) ν H C
    output candidates uniqueIDs ε δ γ _ hε hcollision hdomination hcorrect hsimulation hmeas
  intro w
  rw [FiniteProb.prob_congr _ (fun ω => hrep ω w)]
  exact anonymous_graph_occupancy G hreg ht R (A w) e₀ (hzero w) hD hk hlower hupper

end TreeGeometry
end
end MISLocal
