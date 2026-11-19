import VFTSpanners
import LinearDistancePreservers
import LightSpanners
import DegreeFaultSpanners
import OnlineReachabilityPreservers
import Lean.Util.CollectAxioms

/-! Audit all declarations by defining module, including private/generated
ones and declarations whose namespace differs from their defining module. -/
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in #[`VFTSpanners, `LinearDistancePreservers, `LightSpanners, `DegreeFaultSpanners,
      `OnlineReachabilityPreservers] do
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

#print axioms OnlineReachabilityPreservers.mem_reaches
#print axioms OnlineReachabilityPreservers.forwardPath_spec
#print axioms OnlineReachabilityPreservers.forwardPath_succeeds
#print axioms OnlineReachabilityPreservers.SourceAudit.lemma25_printed_counterexample
#print axioms OnlineReachabilityPreservers.SourceAudit.lemma25_tail_count
#print axioms OnlineReachabilityPreservers.SourceAudit.corrected_fixed_point_iff

#print axioms OnlineReachabilityPreservers.no_earlier_last_arc
#print axioms OnlineReachabilityPreservers.theorem11_sinks
#print axioms OnlineReachabilityPreservers.theorem11_sources
#print axioms OnlineReachabilityPreservers.theorem9_lift
#print axioms OnlineReachabilityPreservers.theorem2_sinks
#print axioms OnlineReachabilityPreservers.theorem2_sources

#print axioms OnlineReachabilityPreservers.backwardCompressed_total
#print axioms OnlineReachabilityPreservers.theorem15_known_budget
#print axioms OnlineReachabilityPreservers.theorem16_index_sensitive
#print axioms OnlineReachabilityPreservers.plannedArcs_prefix
#print axioms OnlineReachabilityPreservers.theorem5_sinks_known_p
#print axioms OnlineReachabilityPreservers.theorem5_sources_known_p
#print axioms OnlineReachabilityPreservers.theorem5_sinks_indexed
#print axioms OnlineReachabilityPreservers.theorem5_sources_indexed
#print axioms OnlineReachabilityPreservers.theorem5_pairwise_rounded
#print axioms OnlineReachabilityPreservers.theorem5_pairwise_limiting_rate
#print axioms OnlineReachabilityPreservers.lemma24_fiber_card
#print axioms OnlineReachabilityPreservers.lemma24_right_monotone
#print axioms OnlineReachabilityPreservers.lemma26_chain_lower
#print axioms OnlineReachabilityPreservers.lemma27_acyclic
#print axioms OnlineReachabilityPreservers.pairwise_initial
#print axioms OnlineReachabilityPreservers.lemma28_from_incidence
#print axioms OnlineReachabilityPreservers.lemma28_mean_lower
#print axioms OnlineReachabilityPreservers.lemma28_scaled_mean_lower
#print axioms OnlineReachabilityPreservers.lemma41_branch_count
#print axioms OnlineReachabilityPreservers.theorem38_root
#print axioms OnlineReachabilityPreservers.theorem38_exponent_limits
#print axioms OnlineReachabilityPreservers.lemma37_acyclic_update
#print axioms OnlineReachabilityPreservers.theorem38_acyclic_iteration
#print axioms OnlineReachabilityPreservers.theorem1_rounded
#print axioms OnlineReachabilityPreservers.theorem1_limiting_rate
#print axioms OnlineReachabilityPreservers.theorem43_exponent_limit
#print axioms OnlineReachabilityPreservers.theorem14_dag_compression
#print axioms OnlineReachabilityPreservers.SourceAudit.lemma14_overlay_counterexample
#print axioms OnlineReachabilityPreservers.offline_pairwise_initial
#print axioms OnlineReachabilityPreservers.lemma37_first_term
#print axioms OnlineReachabilityPreservers.lemma37_third_term
#print axioms OnlineReachabilityPreservers.lemma42_third_term
#print axioms OnlineReachabilityPreservers.lemma42_comparison
#print axioms OnlineReachabilityPreservers.lemma42_acyclic_update
#print axioms OnlineReachabilityPreservers.theorem43_acyclic_iteration
#print axioms OnlineReachabilityPreservers.theorem43_acyclic_limit
#print axioms OnlineReachabilityPreservers.theorem4_rounded
#print axioms OnlineReachabilityPreservers.theorem4_sharp
#print axioms OnlineReachabilityPreservers.lemma42_printed_vertex_exponent_ne
#print axioms OnlineReachabilityPreservers.lemma30_integral_square_sum
#print axioms OnlineReachabilityPreservers.lemma31_acyclic_moment
#print axioms OnlineReachabilityPreservers.lemma32_degree_count
#print axioms OnlineReachabilityPreservers.lemma32_extremal_count
#print axioms OnlineReachabilityPreservers.lemma33_deterministic
#print axioms OnlineReachabilityPreservers.lemma33_expected_count
#print axioms OnlineReachabilityPreservers.lemma34_dyadic_moment
#print axioms OnlineReachabilityPreservers.lemma34_minkowski
#print axioms OnlineReachabilityPreservers.lemma34_minkowski_mean
#print axioms OnlineReachabilityPreservers.lemma34_mean_bucket_moment
#print axioms OnlineReachabilityPreservers.lemma34_off_base_expectation
#print axioms OnlineReachabilityPreservers.source_restricted_square
#print axioms OnlineReachabilityPreservers.lemma35_important_upper
#print axioms OnlineReachabilityPreservers.lemma35_on_base_dyadic_count
#print axioms OnlineReachabilityPreservers.lemma35_on_base_expectation
#print axioms OnlineReachabilityPreservers.lemma36_acyclic_expectation
#print axioms OnlineReachabilityPreservers.sampled_vertex_moment
#print axioms OnlineReachabilityPreservers.SourceAudit.lemma31_printed_intervals_overlap
#print axioms OnlineReachabilityPreservers.SourceAudit.lemma40_printed_intervals_overlap
#print axioms OnlineReachabilityPreservers.regularization_average_caps
#print axioms OnlineReachabilityPreservers.regularization_halfFree
#print axioms OnlineReachabilityPreservers.regularization_free
#print axioms OnlineReachabilityPreservers.lemma40_acyclic_moment
#print axioms OnlineReachabilityPreservers.lemma41_sampled_upper
#print axioms OnlineReachabilityPreservers.lemma20_opt_squared
#print axioms OnlineReachabilityPreservers.lemma20_nontrivial_trace
#print axioms OnlineReachabilityPreservers.lemma22_hub_count
#print axioms OnlineReachabilityPreservers.thickSampleCount_probability
#print axioms OnlineReachabilityPreservers.hubPreserver_balanced_bound
#print axioms OnlineReachabilityPreservers.thinCoverRun_bound
#print axioms OnlineReachabilityPreservers.thinCoverRun_prefix
#print axioms OnlineReachabilityPreservers.fastThinViolation_eq_none
#print axioms OnlineReachabilityPreservers.unitAugmentations_count
#print axioms OnlineReachabilityPreservers.thinCoverLoop_updates
#print axioms OnlineReachabilityPreservers.roundedThin_cut_probability
#print axioms OnlineReachabilityPreservers.thinRoundRun_correct
#print axioms OnlineReachabilityPreservers.thinRoundRun_competitive
#print axioms OnlineReachabilityPreservers.assembledSteiner_empty
#print axioms OnlineReachabilityPreservers.assembledSteiner_prefix
#print axioms OnlineReachabilityPreservers.assembledSteiner_correct
#print axioms OnlineReachabilityPreservers.assembledSteiner_mean_transfer
#print axioms OnlineReachabilityPreservers.lemma29_square_sum
#print axioms OnlineReachabilityPreservers.SourceAudit.splitExample_bridge_free
#print axioms OnlineReachabilityPreservers.SourceAudit.splitExample_creates_half_four
