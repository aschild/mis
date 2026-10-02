import MISLocal.GraphOccupancy
import MISLocal.TapeAveraging
import MISLocal.Obstruction

/-! The fixed-tape/averaging step now uses the proved graph occupancy theorem
as a black box. Tape spaces can be infinite. No per-fixed-tape occupancy bound
is assumed. The LOCAL simulation, collision and domination interfaces remain
explicit; this module is not an unconditional asymptotic LOCAL lower bound. -/

open MeasureTheory

namespace MISLocal
noncomputable section
namespace TreeGeometry

variable {V W : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [MeasurableSpace W]
    {d n k : ℕ} {Q : V → Type} [∀ v, Fintype (Q v)]

/-- Averaging over arbitrary tape tables costs nothing in the occupancy
bound. Independence is required of the graph/private inputs, not of the
derived outputs or of neighboring execution events. -/
theorem averaged_graph_occupancy
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    (R : ∀ v, FiniteProb (Q v)) (ν : Measure W) [IsProbabilityMeasure ν]
    (U : W → V → (∀ i, matrixPrivateType G k Q i) → Option (Fin k))
    (hlocal : ∀ w v, ReadsOnly (U w v) (privateReads (seen G (n+1)) v))
    (hhom : ∀ w, ViewHomogeneous (FiniteProb.pi (matrixPrivateProbability G k R)) (U w)
      (fun j v => observeInputs (rawView (V := V) (seen G (n+1-j) v)))
      (fun j e => observeInputs (rawView (V := V) (sharedEdges G (n+1-j) e)))
      (edgeLeft G) (edgeRight G))
    (e₀ : G.edgeSet)
    (hzero : ∀ w, (FiniteProb.pi (matrixPrivateProbability G k R)).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),U w (edgeLeft G e₀) ω,U w (edgeRight G e₀) ω)) = 0)
    (hmeas : ∀ ω, MeasurableSet {w | U w (edgeLeft G e₀) ω ≠ none})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (FiniteProb.pi (matrixPrivateProbability G k R)).expect
      (fun ω => ν.real {w | U w (edgeLeft G e₀) ω ≠ none}) ≤
        occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  exact average_fixed_tape_bound _ ν _ hmeas _ (fun w =>
    graph_occupancy G hreg ht R (U w) (hlocal w) (hhom w) e₀ (hzero w) hD hk hlower hupper)

/-- A finite LOCAL obstruction with the old `hfixed` occupancy premise
removed. Instead, the candidate process is represented by actual local,
homogeneous, zero-conflict label outputs, to which `graph_occupancy` applies.
Simulation and its error estimates still have to be proved for the chosen
blow-up construction. -/
theorem graph_finite_obstruction {X : Type*}
    (hreg : ∀ v, G.degree v = d+1)
    (ht : ∀ e : G.edgeSet, (G.induce (edgeRegion G e (n+1))).IsTree)
    (R : ∀ v, FiniteProb (Q v)) (ν : Measure W) [IsProbabilityMeasure ν]
    (H : (∀ i, matrixPrivateType G k Q i) → SimpleGraph X) (C : Set X)
    (output candidates : (∀ i, matrixPrivateType G k Q i) → W → Set X)
    (uniqueIDs : (∀ i, matrixPrivateType G k Q i) → Prop)
    (U : W → V → (∀ i, matrixPrivateType G k Q i) → Option (Fin k))
    (hlocal : ∀ w v, ReadsOnly (U w v) (privateReads (seen G (n+1)) v))
    (hhom : ∀ w, ViewHomogeneous (FiniteProb.pi (matrixPrivateProbability G k R)) (U w)
      (fun j v => observeInputs (rawView (V := V) (seen G (n+1-j) v)))
      (fun j e => observeInputs (rawView (V := V) (sharedEdges G (n+1-j) e)))
      (edgeLeft G) (edgeRight G))
    (e₀ : G.edgeSet)
    (hzero : ∀ w, (FiniteProb.pi (matrixPrivateProbability G k R)).prob (fun ω =>
      selectedConflict (fun M a b => M (a,b)=true)
        (ω (Sum.inl e₀),U w (edgeLeft G e₀) ω,U w (edgeRight G e₀) ω)) = 0)
    (hrep : ∀ ω w, Occupies C (repair (H ω) (candidates ω w)) ↔ U w (edgeLeft G e₀) ω ≠ none)
    (ε δ γ : ℝ) (hε : ε ≤ 1)
    (hcollision : (FiniteProb.pi (matrixPrivateProbability G k R)).prob (fun ω => ¬uniqueIDs ω) ≤ δ)
    (hdomination : (FiniteProb.pi (matrixPrivateProbability G k R)).prob
      (fun ω => ExternallyDominatable (H ω) C) ≤ γ)
    (hcorrect : ∀ ω, 1-ε ≤ ν.real {w | Maximal (H ω).IsIndepSet (output ω w)})
    (hsimulation : ∀ ω, uniqueIDs ω → ∀ w v, v ∈ C → ∀ x,
      x = v ∨ (H ω).Adj v x → (x ∈ candidates ω w ↔ x ∈ output ω w))
    (hmeas : ∀ ω, MeasurableSet {w | Occupies C (repair (H ω) (candidates ω w))})
    (hD : 1048576 ≤ d+1) (hk : 1 ≤ k)
    (hlower : ((d+1:ℕ):ℝ) ≤ Real.log (k:ℝ))
    (hupper : Real.log (k:ℝ) ≤ ((d+1:ℕ):ℝ)^2) :
    (1-ε)*(1-δ-γ) ≤ occupancyCap (n+1) ((d+1:ℕ):ℝ) := by
  apply finite_obstruction (FiniteProb.pi (matrixPrivateProbability G k R)) ν H C output
    candidates uniqueIDs ε δ γ _ hε hcollision hdomination hcorrect hsimulation hmeas
  intro w
  rw [FiniteProb.prob_congr _ (fun ω => hrep ω w)]
  exact graph_occupancy G hreg ht R (U w) (hlocal w) (hhom w) e₀ (hzero w) hD hk hlower hupper

end TreeGeometry
end
end MISLocal
