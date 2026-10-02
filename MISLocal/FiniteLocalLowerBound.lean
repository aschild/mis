import MISLocal.PowerBallEstimates

/-! A finite LOCAL lower bound with every geometric, probability and parameter
premise discharged. Program measurability and MIS correctness are the only
algorithmic assumptions. No skeleton-existence or reduction hypothesis remains. -/

open MeasureTheory
open scoped Classical
namespace MISLocal
noncomputable section

/-- Ordinary measurability of the program's output as a function of its tapes.
This condition asserts no success, independence, symmetry or lower bound. -/
def MeasurableProgram {n : ℕ} {Tape State : Type} [MeasurableSpace Tape]
    (A : UniformLocalProtocol n Tape State) (T : ℕ) : Prop :=
  ∀ (X : Type) [Fintype X] (G : SimpleGraph X) (ids : X → Fin n) (v : X),
    MeasurableSet {W : Fin n → Tape | v ∈ A.candidates G ids W T}

namespace PowerSize
open TreeGeometry
theorem finite_local_round_bound {Tape State : Type} [MeasurableSpace Tape]
    (s T : ℕ) (hs : 20 ≤ s) (A : UniformLocalProtocol (size s) Tape State)
    (ν : Measure (Fin (size s) → Tape)) [IsProbabilityMeasure ν]
    (hmeas : MeasurableProgram A T)
    (hcorrect : ∀ K : SimpleGraph (Fin (size s)),
      (2/3:ℝ) ≤ ν.real {W | Maximal K.IsIndepSet (A.candidates K id W T)}) :
    degree s < 20000*(T+3)*(s+1) := by
  by_contra hfail
  have hsmall : 20000*(T+3)*(s+1) ≤ degree s := Nat.le_of_not_gt hfail
  have hD : 1048576 ≤ degree s := by
    have hp : (2:ℕ)^20 ≤ 2^s := pow_le_pow_right' (by norm_num) hs
    norm_num at hp
    exact hp
  have hd10 : 10 ≤ degree s := by omega
  let L := T+5
  have hL : 1 ≤ L := by omega
  let G := FiniteTree.graph (degree s) L hL
  letI : Nonempty (FiniteTree.Vertex (degree s) L) := ⟨1⟩
  have hreg : ∀ v, G.degree v = degree s := FiniteTree.graph_regular hL
  have hregle : ∀ v, G.degree v ≤ degree s := fun v => (hreg v).le
  have ht : ∀ e : G.edgeSet, (G.induce (TreeGeometry.edgeRegion G e (T+3))).IsTree :=
    FiniteTree.graph_edgeRegion_tree hL (by omega)
  let color : Fin (degree s) := ⟨0,by omega⟩
  let e : G.edgeSet := ⟨s(1,FiniteTree.generator L color),⟨color,by simp⟩⟩
  obtain ⟨pack⟩ := packing_exists hd10
  have hk : 1 ≤ 2*halfClique (degree s) := by
    have hp : 1 ≤ halfClique (degree s) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hd : degree s-1+1 = degree s := Nat.sub_add_cancel (by omega)
  have hlog := clique_log_bounds hd10
  have ho := TreeGeometry.local_size_obstruction G pack A ν T (d := degree s-1)
    (by intro v; rw [hd]; exact hreg v) ht e
    (ball_fits G hregle (TreeGeometry.edgeLeft G e) hsmall) (1/3) (by norm_num)
    (by intro K; convert hcorrect K using 1; norm_num)
    (fun M z => hmeas _ (cliqueBlowup G M) (extractedIdentifiers G pack M) z)
    (by simpa only [hd] using hD) hk
    (by simpa only [hd] using hlog.1) (by simpa only [hd] using hlog.2)
  rw [hd] at ho
  have hδ := collision_error_small G hregle (TreeGeometry.edgeLeft G e) hsmall
  have hγ := domination_error_small hd10
  have hhalf := obstruction_at_least_half (ε := (1/3:ℝ)) (by norm_num) (by linarith :
    TreeGeometry.localCollisionError G (m := halfClique (degree s)) (b := bits (degree s)) T
      (TreeGeometry.edgeLeft G e) + TreeGeometry.localDominationError (m := halfClique (degree s))
      (degree s) ≤ 1/4)
  have hcap := small_occupancy_cap hsmall
  linarith
end PowerSize
end
end MISLocal
