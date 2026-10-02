import MISLocal.Identifiers
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Reindexing independent, possibly infinite random tapes

Only the vertex and identifier index sets are finite. `Tape` is any measurable
space with a probability measure. The theorem preserves the full product measure,
so it establishes joint independence, not just correct marginal distributions.
-/

open MeasureTheory

namespace MISLocal
noncomputable section

theorem tape_reindex_measurePreserving {V ID Tape : Type*}
    [Fintype V] [Fintype ID] [MeasurableSpace Tape]
    (ρ : Measure Tape) [IsProbabilityMeasure ρ] (ids : V ≃ ID) :
    MeasurePreserving (reindexTapes (Tape := Tape) ids)
      (Measure.pi (fun _ : ID => ρ)) (Measure.pi (fun _ : V => ρ)) := by
  convert measurePreserving_piCongrLeft (fun _ : V => ρ) ids.symm using 1
  funext W v
  simp [reindexTapes, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft']

/-- For each fixed graph, a graph-dependent legal ID completion still preserves
the product tape distribution. `ids` has no tape-table argument. -/
theorem graph_dependent_tape_reindex {Ω V ID Tape : Type*}
    [Fintype V] [Fintype ID] [MeasurableSpace Tape]
    (ρ : Measure Tape) [IsProbabilityMeasure ρ] (ids : Ω → V ≃ ID) (g : Ω) :
    (Measure.pi (fun _ : ID => ρ)).map (reindexTapes (Tape := Tape) (ids g)) =
      Measure.pi (fun _ : V => ρ) :=
  (tape_reindex_measurePreserving ρ (ids g)).map_eq

end
end MISLocal
