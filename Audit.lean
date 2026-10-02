import MISLocal
import Lean.Util.CollectAxioms

/-!
The audit checks transitive dependencies of EVERY theorem in MISLocal and
the public definitions explicitly listed below.
It raises a Lean elaboration error for any axiom beyond the three standard
classical foundations below. A printed success word is never a substitute
for successful compilation. This audit does not assert that a conditional
theorem has had all of its mathematical hypotheses discharged.
-/

open Lean Elab Command

elab "#audit_mislocal" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let definitions : Array Name := #[
    ``MISLocal.bit, ``MISLocal.FiniteProb, ``MISLocal.FiniteProb.expect,
    ``MISLocal.FiniteProb.prob, ``MISLocal.FiniteProb.uniform,
    ``MISLocal.repair, ``MISLocal.Occupies, ``MISLocal.ExternallyDominatable,
    ``MISLocal.completeIDs, ``MISLocal.reindexTapes,
    ``MISLocal.sumSplit, ``MISLocal.jointSumSplit, ``MISLocal.occupancyCap,
    ``MISLocal.FiniteProb.pointMass, ``MISLocal.FiniteProb.map,
    ``MISLocal.FiniteProb.entropy, ``MISLocal.FiniteProb.entropyOf,
    ``MISLocal.FiniteProb.condEntropy, ``MISLocal.FiniteProb.Dominated,
    ``MISLocal.FiniteProb.kl, ``MISLocal.massBudget,
    ``MISLocal.FiniteProb.conditionalProduct, ``MISLocal.FiniteProb.given,
    ``MISLocal.FiniteProb.projectedPair, ``MISLocal.selectedConflict,
    ``MISLocal.classifiedOutput, ``MISLocal.FiniteProb.hellingerSq,
    ``MISLocal.InBall, ``MISLocal.LocalProtocol, ``MISLocal.LocalProtocol.run,
    ``MISLocal.LocalProtocol.candidates, ``MISLocal.UniformLocalProtocol, ``MISLocal.FiniteProb.product,
    ``MISLocal.bestList, ``MISLocal.FiniteProb.outputList, ``MISLocal.FiniteProb.listTail,
    ``MISLocal.FiniteProb.tail, ``MISLocal.FiniteProb.pi, ``MISLocal.FiniteProb.Independent,
    ``MISLocal.FiniteProb.IndependentEvents, ``MISLocal.FiniteProb.eventCount,
    ``MISLocal.FiniteProb.eventMean, ``MISLocal.FiniteProb.labelWeight,
    ``MISLocal.FiniteProb.totalListWeight, ``MISLocal.FiniteProb.listCaptures,
    ``MISLocal.FiniteProb.branchEligible, ``MISLocal.FiniteProb.branchList,
    ``MISLocal.FiniteProb.fairBits, ``MISLocal.FiniteProb.rectangleCount,
    ``MISLocal.FiniteProb.exceptionalMatrix, ``MISLocal.restrictOutput,
    ``MISLocal.FiniteProb.keptOutput, ``MISLocal.FiniteProb.deletedOutput,
    ``MISLocal.binaryEntropy, ``MISLocal.FiniteProb.DoesNotRead,
    ``MISLocal.observeInputs, ``MISLocal.FiniteProb.revealGain,
    ``MISLocal.revealPrefix, ``MISLocal.SourceCharge,
    ``MISLocal.ProductInputGeometry, ``MISLocal.EndpointTransport,
    ``MISLocal.InputRelabeling, ``MISLocal.NamedLocalView,
    ``MISLocal.TreeGeometry.OrientedRegionIso]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  -- Reuse Lean's own traversal state across roots. A dependency already
  -- traversed in this same immutable checked environment need not be visited
  -- again. This changes runtime, not the set of axioms that is checked.
  let mut traversal : CollectAxioms.State := {}
  for (name, info) in env.constants do
    if (`MISLocal).isPrefixOf name &&
        (info.isTheorem || (info.isDefinition && !name.isInternal) || definitions.contains name) then
      unless (env.checked.get.find? name).isSome do
        throwError "Declaration is absent from the checked kernel environment: {name}"
      let (_, next) := ((CollectAxioms.collect name).run env).run traversal
      traversal := next
      for ax in traversal.axioms do
        unless allowed.contains ax do
          throwError "Forbidden axiom dependency: {name} depends on {ax}"
      checked := checked + 1
      if info.isTheorem then
        theorems := theorems + 1
  unless checked > 0 && theorems > 0 do
    throwError "Empty audit: the MISLocal modules were not imported"
  logInfo m!"Audited {checked} theorem/definition roots, including {theorems} theorems."
  logInfo "Only propext, Classical.choice, and Quot.sound were allowed."

#audit_mislocal

#print axioms MISLocal.FiniteTree.graph_edgeRegion_tree
#print axioms MISLocal.realization_forces_repaired_occupancy
#print axioms MISLocal.TreeGeometry.local_size_obstruction
#print axioms MISLocal.PowerSize.finite_local_round_bound
#print axioms MISLocal.randomized_LOCAL_MIS_not_littleO
#print axioms MISLocal.randomized_LOCAL_MIS_iid_not_littleO
#check MISLocal.MeasurableProgram
#check MISLocal.PowerSize.finite_local_round_bound
#check MISLocal.randomized_LOCAL_MIS_iid_not_littleO

#print axioms MISLocal.outgoing_sums_jointly_uniform
#print axioms MISLocal.local_collision_bound_of_pairwise_independent
#print axioms MISLocal.completeIDs_bijective
#print axioms MISLocal.tape_reindex_measurePreserving
#print axioms MISLocal.average_fixed_tape_bound
#print axioms MISLocal.occupancy_transfer
#print axioms MISLocal.finite_obstruction
#print axioms MISLocal.conditional_round_lower_bound
#print axioms MISLocal.FiniteProb.zero_event_le_kl
#print axioms MISLocal.FiniteProb.entropy_submodular
#print axioms MISLocal.FiniteProb.copying_potential_nonincrease
#print axioms MISLocal.FiniteProb.conditional_rare_entropy_le
#print axioms MISLocal.FiniteProb.classified_projected_budget
#print axioms MISLocal.occupancy_from_reduction_estimates
#print axioms MISLocal.FiniteProb.sqrt_event_le
#print axioms MISLocal.completed_ID_simulation
#print axioms MISLocal.zero_radius_conflict
#print axioms MISLocal.FiniteProb.branch_transfer
#print axioms MISLocal.FiniteProb.dense_boolean_tail_product
#print axioms MISLocal.FiniteProb.exceptional_matrix_probability
#print axioms MISLocal.FiniteProb.conditional_edge_vertex_entropy
#print axioms MISLocal.FiniteProb.symmetric_conditional_edge_entropy
#print axioms MISLocal.truncation_moment_bound

/- Print the hypotheses too: checking only the conclusion is insufficient. -/
#check MISLocal.conditional_round_lower_bound
#check MISLocal.FiniteProb.classified_projected_budget
#check MISLocal.occupancy_from_reduction_estimates
#check MISLocal.completed_ID_simulation
#check MISLocal.FiniteProb.branch_transfer
#check MISLocal.FiniteProb.symmetric_conditional_edge_entropy
#print axioms MISLocal.TreeGeometry.sourceChargeOfReaderTrees
#print axioms MISLocal.FiniteProb.symmetric_table_entropy
#print axioms MISLocal.FiniteProb.weighted_branch_failures
#print axioms MISLocal.FiniteProb.ancestor_mass_partition
#check MISLocal.TreeGeometry.sourceChargeOfReaderTrees
#check MISLocal.FiniteProb.symmetric_table_entropy
#check MISLocal.FiniteProb.truncation_from_local_moments
#print axioms MISLocal.FiniteProb.sampled_is_projectedPair
#print axioms MISLocal.FiniteProb.survivor_transport
#print axioms MISLocal.FiniteProb.finite_occupancy
#print axioms MISLocal.TreeGeometry.graphInputGeometry
#print axioms MISLocal.TreeGeometry.graph_occupancy
#print axioms MISLocal.viewHomogeneous_of_input_relabelings
#print axioms MISLocal.TreeGeometry.averaged_graph_occupancy
#print axioms MISLocal.TreeGeometry.graph_finite_obstruction
#check MISLocal.FiniteProb.finite_occupancy
#check MISLocal.TreeGeometry.graph_occupancy
#check MISLocal.TreeGeometry.graph_finite_obstruction
#print axioms MISLocal.TreeGeometry.regularRegionIso
#print axioms MISLocal.TreeGeometry.runAnonymous_zero_same_coin
#print axioms MISLocal.TreeGeometry.anonymous_homogeneous
#print axioms MISLocal.TreeGeometry.anonymous_graph_occupancy
#print axioms MISLocal.TreeGeometry.averaged_anonymous_graph_occupancy
#print axioms MISLocal.TreeGeometry.anonymous_graph_finite_obstruction
#check MISLocal.AnonymousRule
#check MISLocal.TreeGeometry.anonymous_homogeneous
#check MISLocal.TreeGeometry.anonymous_graph_occupancy
#check MISLocal.TreeGeometry.anonymous_graph_finite_obstruction

#print axioms MISLocal.TreeGeometry.extractedIdentifiers_jointly_uniform
#print axioms MISLocal.TreeGeometry.localAnonymousRule_representation
#print axioms MISLocal.TreeGeometry.completed_candidate_simulation
#print axioms MISLocal.TreeGeometry.external_domination_probability
#print axioms MISLocal.TreeGeometry.concrete_finite_obstruction
#check MISLocal.UniformLocalProtocol
#check MISLocal.TreeGeometry.concrete_finite_obstruction
