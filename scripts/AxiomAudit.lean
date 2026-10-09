import VFTSpanners
import LinearDistancePreservers
import LightSpanners
import DegreeFaultSpanners
import Lean.Util.CollectAxioms

/-! Audit all declarations by defining module, including private/generated
ones and declarations whose namespace differs from their defining module. -/
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in #[`VFTSpanners, `LinearDistancePreservers, `LightSpanners, `DegreeFaultSpanners] do
    let mut count : Nat := 0
    for (name, _) in env.constants.toList do
      let fromProject := match env.getModuleIdxFor? name with
        | some idx => match moduleNames[idx.toNat]? with
          | some moduleName => root.isPrefixOf moduleName
          | none => false
        | none => false
      if fromProject then
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Disallowed axiom {ax} in {name}"
    if count == 0 then
      throwError "No declarations found for {root}; the audit did not run"
    logInfo m!"Axiom audit passed: {count} declarations defined in {root} modules; allowed axioms: {allowed}"

#print axioms VFTSpanners.vft_greedy_theorem_one
#print axioms VFTSpanners.covered_iff_distance
#print axioms VFTSpanners.vft_greedy_zero_faults
#print axioms VFTSpanners.corollary_two_from_moore
#print axioms VFTSpanners.moore_edge_bound
#print axioms VFTSpanners.extremalEdges_moore
#print axioms VFTSpanners.corollary_two
#print axioms LinearDistancePreservers.theorem_one_of_consistent_selection
#print axioms LinearDistancePreservers.theorem_one
#print axioms LinearDistancePreservers.ConsistentTiebreaking.optimal_subpaths_eq
#print axioms LinearDistancePreservers.LazyTreeSelection.exists_lazy_tree
#print axioms LinearDistancePreservers.LazyTreeSelection.branchEdges_le_two_demands
#print axioms LinearDistancePreservers.exists_favorable_cut
#print axioms LinearDistancePreservers.theorem_two
#print axioms LinearDistancePreservers.matchingNumber_subquadratic
#print axioms LinearDistancePreservers.LazyEdges.class_is_induced_matching
#print axioms LinearDistancePreservers.WeightedConstruction.designated_not_shortest
#print axioms LinearDistancePreservers.ModularGraph.Walk.optimal
#print axioms LinearDistancePreservers.ModularGraph.Walk.unique_vertex_sequence
#print axioms LinearDistancePreservers.ModularGraph.edge_count
#print axioms LinearDistancePreservers.ModularGraph.paths_through_card
#print axioms LinearDistancePreservers.WeightedDigraph.exists_shortest_of_distance_ne_top
#print axioms LinearDistancePreservers.WeightedDigraph.forces_edges_of_unique_shortest
#print axioms LinearDistancePreservers.WeightedNativeForcing.eq_of_covers
#print axioms LinearDistancePreservers.ModularGraph.canonical_unique
#print axioms LinearDistancePreservers.ModularGraph.canonical_edge_owner_unique
#print axioms LinearDistancePreservers.ModularGraph.subset_preserver_edge_count
#print axioms LinearDistancePreservers.ObstacleProduct.fullWalk_shortest
#print axioms LinearDistancePreservers.ObstacleProduct.preserver_edge_count_of_unique
#print axioms LinearDistancePreservers.ModularObstacle.edge_count
#print axioms LinearDistancePreservers.WeightedNativeForcing.exists_path_perturbation
#print axioms LinearDistancePreservers.ConvexDirections.modular_sphere_unique
#print axioms LinearDistancePreservers.ObstacleProduct.factor_left_right
#print axioms LinearDistancePreservers.ObstacleProduct.fullWalk_unique
#print axioms LinearDistancePreservers.ObstacleProduct.preserver_edge_count
#print axioms LinearDistancePreservers.ObstacleProduct.separated_optimal
#print axioms LinearDistancePreservers.ModularObstacle.full_optimal
#print axioms LinearDistancePreservers.ModularObstacle.preserver_edge_count
#print axioms LinearDistancePreservers.TheoremThree.family_lower_bound
#print axioms LinearDistancePreservers.DirectionGraph.canonical_unique
#print axioms LinearDistancePreservers.DirectionGraph.sphere_rigid
#print axioms LinearDistancePreservers.PreserverPadding.distance_comap
#print axioms LinearDistancePreservers.PreserverPadding.pad
#print axioms LinearDistancePreservers.PathLowerBound.exists_path_witness
#print axioms LinearDistancePreservers.LowerBoundParameters.product_parameters
#print axioms LinearDistancePreservers.TheoremThree.exact_size_lower_bound
#print axioms LinearDistancePreservers.TheoremThree.bounded_range_lower_bound
#print axioms LinearDistancePreservers.DirectionGraph.graph_edge_count
#print axioms LinearDistancePreservers.DirectionGraph.canonical_edge_owner_unique
#print axioms LinearDistancePreservers.DirectionGraph.canonical_incidence
#print axioms LinearDistancePreservers.DirectionGraph.convexPosition_rigid
#print axioms LinearDistancePreservers.DirectionObstacle.outer_unique
#print axioms LinearDistancePreservers.DirectionObstacle.inner_unique
#print axioms LinearDistancePreservers.DirectionObstacle.terminals_card
#print axioms LinearDistancePreservers.DirectionObstacle.subset_preserver_edge_count
#print axioms LinearDistancePreservers.DirectionGraph.canonical_support_injective

#print axioms LightSpanners.greedy_isSpanner
#print axioms LightSpanners.greedy_weightedGirth
#print axioms LightSpanners.bucket_budget
#print axioms LightSpanners.sampling_bootstrap

#print axioms DegreeFaultSpanners.theorem_five_uniform_parameters
#print axioms DegreeFaultSpanners.isDegreeFaultSpanner_iff_edist
#print axioms LinearDistancePreservers.BehrendPorts.exists_ports_of_exp
#print axioms LinearDistancePreservers.BehrendPorts.roth_capacity
#print axioms LinearDistancePreservers.BehrendPorts.outer_unique
#print axioms LinearDistancePreservers.SphereDirections.exists_directions
#print axioms LinearDistancePreservers.UnweightedPadding.edist_comap
#print axioms LinearDistancePreservers.UnweightedPadding.pad
#print axioms LinearDistancePreservers.BehrendProduct.exists_product
#print axioms LinearDistancePreservers.BehrendProduct.sphere_lower_bound
#print axioms LinearDistancePreservers.BehrendProduct.integer_lower_bound
#print axioms LinearDistancePreservers.TheoremFourRateAudit.log_polynomial_ratio
#print axioms LinearDistancePreservers.TheoremFourRateAudit.logRatio_le
#print axioms LinearDistancePreservers.TheoremFourRateAudit.suppressed_expression_le
#print axioms LinearDistancePreservers.UnweightedClique.complete_rigid
#print axioms LinearDistancePreservers.UnweightedClique.clique_lower_bound
#print axioms LinearDistancePreservers.TheoremFourDense.displayed_bound_of_small_deficit
#print axioms LinearDistancePreservers.ConvexChains.exposed
#print axioms LinearDistancePreservers.ConvexChains.average_rigid
#print axioms LinearDistancePreservers.ConvexChains.exists_directions
