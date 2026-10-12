import MinorFreeSpanners
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let root := `MinorFreeSpanners
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx => match modules[idx.toNat]? with
        | some mod => root.isPrefixOf mod
        | none => false
      | none => false
    if fromProject then
      count := count + 1
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then throwError "No MinorFreeSpanners declarations found"
  logInfo m!"Axiom audit passed for {count} MinorFreeSpanners declarations; allowed axioms: {allowed}"

#print axioms MinorFreeSpanners.claim19_counterexample_with_source_hypotheses
#print axioms MinorFreeSpanners.claim19_corrected
#print axioms MinorFreeSpanners.cluster_threshold_repair
#print axioms MinorFreeSpanners.theorem11
#print axioms MinorFreeSpanners.high_girth_spanner_eq
#print axioms MinorFreeSpanners.cliqueMinorFree_two_iff
#print axioms MinorFreeSpanners.cliqueMinorFree_of_edges
#print axioms MinorFreeSpanners.density_increment_exponent

#print axioms MinorFreeSpanners.MinorModel.comp
#print axioms MinorFreeSpanners.MinorModel.exists_component
#print axioms MinorFreeSpanners.cliqueMinorFree_of_component_edges
#print axioms MinorFreeSpanners.GirthAbove.of_components
#print axioms MinorFreeSpanners.copied_core_lower_bound
#print axioms MinorFreeSpanners.MinorModel.singleton_branch_degree
#print axioms MinorFreeSpanners.CliqueMinorFree.subdivideEdge
#print axioms MinorFreeSpanners.density_increment_linear_loss

#print axioms MinorFreeSpanners.minor_unit_tree_reduction_of_mst
#print axioms MinorFreeSpanners.padGraph.minorFree
#print axioms MinorFreeSpanners.padGraph.girth
#print axioms MinorFreeSpanners.exact_size_core_lower_bound
#print axioms MinorFreeSpanners.replacement_walk_gap
#print axioms MinorFreeSpanners.ClusterFamily.minorModel
#print axioms MinorFreeSpanners.ClusterFamily.no_heavy_loop
#print axioms MinorFreeSpanners.ClusterFamily.heavy_edge_unique

#print axioms MinorFreeSpanners.ClusterFamily.lift_walk_bounded_on_edges
#print axioms MinorFreeSpanners.ClusterFamily.exists_bridge_with_weight
#print axioms MinorFreeSpanners.closed_trail_remove_edge
#print axioms MinorFreeSpanners.ClusterFamily.girth
#print axioms MinorFreeSpanners.claim23_for_cluster_family

#print axioms MinorFreeSpanners.girth_conjecture_sparse_lower_bound_all_h
#print axioms MinorFreeSpanners.star_sparse_lower_bound
#print axioms MinorFreeSpanners.exists_edge_trim

#print axioms MinorFreeSpanners.rootedCompletion.connected
#print axioms MinorFreeSpanners.rootedCompletion.girth
#print axioms MinorFreeSpanners.rootedCompletion.minorFree
#print axioms MinorFreeSpanners.unit_mst_exists
#print axioms MinorFreeSpanners.girth_conjecture_connected_lower_bound

#print axioms MinorFreeSpanners.triangle_minor_of_cycle
#print axioms MinorFreeSpanners.minor_unit_tree_reduction_of_mst_all_h
#print axioms MinorFreeSpanners.MinorModel.IsBounded.comp
#print axioms MinorFreeSpanners.MinorModel.IsBounded.exists_host_subgraph
#print axioms MinorFreeSpanners.postle_small_dense_or_unmated
#print axioms MinorFreeSpanners.postle_bounded_minor_dense_or_unmated
#print axioms MinorFreeSpanners.postle_vertex_budget
#print axioms MinorFreeSpanners.postle_displayed_rounding_step_counterexample
#print axioms MinorFreeSpanners.postle_bipartite_density_budget

#print axioms MinorFreeSpanners.exists_left_regular_subgraph
#print axioms MinorFreeSpanners.postle_subgraph_dense_or_unmated
#print axioms MinorFreeSpanners.MateFreeOn.insert_center
#print axioms MinorFreeSpanners.contractEdgeModel_bounded
#print axioms MinorFreeSpanners.contractEdge_edge_count
#print axioms MinorFreeSpanners.exists_minimal_dense_minor
#print axioms MinorFreeSpanners.exists_dense_minor_neighborhood
#print axioms MinorFreeSpanners.deletionConnected_of_degree

#print axioms MinorFreeSpanners.robust_or_small_robust_induced
#print axioms MinorFreeSpanners.exists_small_dominating_set
#print axioms MinorFreeSpanners.connected_exists_walk_length_le_eleven
#print axioms MinorFreeSpanners.robust_core_clique_minor
#print axioms MinorFreeSpanners.clique_minor_of_logarithmic_density
#print axioms MinorFreeSpanners.CliqueMinorFree.edge_count_le_logarithmic

#print axioms MinorFreeSpanners.exists_full_star_minor
#print axioms MinorFreeSpanners.StaticStarAlternatingRoute.augment
#print axioms MinorFreeSpanners.reachableStarCenters_boundary

#print axioms MinorFreeSpanners.unmated_small_left_full_star_contraction
#print axioms MinorFreeSpanners.IsStarPacking.fullContraction_card

#print axioms MinorFreeSpanners.regularize_dense_or_mate_free_stars

#print axioms MinorFreeSpanners.IsStarPacking.fullContraction_edge_loss

#print axioms MinorFreeSpanners.exists_small_star_restriction

#print axioms MinorFreeSpanners.exists_minimum_bad_star_family

#print axioms MinorFreeSpanners.IsStarPacking.selected_edge_fiber_card

#print axioms MinorFreeSpanners.MateFreeOn.ordered_collision_budget

#print axioms MinorFreeSpanners.ordered_collision_absorption

#print axioms MinorFreeSpanners.IsStarPacking.twoStarLeafSwap_valid

#print axioms MinorFreeSpanners.IsStarPacking.twoStarLeafSwap_mateFree

#print axioms MinorFreeSpanners.exists_left_regular_between

#print axioms MinorFreeSpanners.IsStarPacking.exists_regular_supergraph_of_forest

#print axioms MinorFreeSpanners.IsStarPacking.starForestSubgraph_acyclic

#print axioms MinorFreeSpanners.IsStarPacking.starForest_edge_count

#print axioms MinorFreeSpanners.IsStarPacking.neighbor_star_union_card

#print axioms MinorFreeSpanners.IsStarPacking.selected_fiber_surplus_le

#print axioms MinorFreeSpanners.IsStarPacking.matedStarCenters_bound

#print axioms MinorFreeSpanners.not_matedStarCenters_union_mateFree

#print axioms MinorFreeSpanners.unmatedBadCenters_card

#print axioms MinorFreeSpanners.badForestPairs_card

#print axioms MinorFreeSpanners.IsStarPacking.badForestPairs_actual_edges

#print axioms MinorFreeSpanners.badForestOutgoing_card

#print axioms MinorFreeSpanners.badForestPairs_loss_of_removed_leaf

#print axioms MinorFreeSpanners.exists_family_with_unmated_swap_gain

#print axioms MinorFreeSpanners.IsStarPacking.twoStarLeafSwap_new_bad_common_neighbor

#print axioms MinorFreeSpanners.IsStarPacking.swapNewBadNoInserted_card_le_mateFree

#print axioms MinorFreeSpanners.IsStarPacking.twoStarLeafSwap_bad_selected_fiber_two

#print axioms MinorFreeSpanners.IsStarPacking.newNoInsertedWitnesses_card_le_mateFree

#print axioms MinorFreeSpanners.IsStarPacking.swapped_branch_subset_witness_vertices

#print axioms MinorFreeSpanners.IsStarPacking.inserted_left_witness_count

#print axioms MinorFreeSpanners.IsStarPacking.inserted_right_witness_count

#print axioms MinorFreeSpanners.IsStarPacking.new_witness_cover

#print axioms MinorFreeSpanners.IsStarPacking.new_witness_induced_budget

#print axioms MinorFreeSpanners.exists_family_with_unmated_induced_degree_budget

#print axioms MinorFreeSpanners.degree_sum_two_injections

#print axioms MinorFreeSpanners.partner_degree_quadratic

#print axioms MinorFreeSpanners.exists_family_with_unmated_dense_witness

#print axioms MinorFreeSpanners.exists_dense_induced_or_unmated_leaf_bound

#print axioms MinorFreeSpanners.badStarPairCount_le_incidence_budget

#print axioms MinorFreeSpanners.exists_dense_induced_or_bad_pair_budget

#print axioms MinorFreeSpanners.IsStarPacking.branch_edge_fiber

#print axioms MinorFreeSpanners.IsStarPacking.selected_residual_fiber_surplus

#print axioms MinorFreeSpanners.quotient_surplus_le_ordered_pairs

#print axioms MinorFreeSpanners.IsStarPacking.full_ordered_fiber_loss_le

#print axioms MinorFreeSpanners.IsStarPacking.fullContraction_edges_ge_budget

#print axioms MinorFreeSpanners.IsStarPacking.fullContraction_edges_ge_mateFree_budget

#print axioms MinorFreeSpanners.exists_dense_induced_or_clean_star_contraction

#print axioms MinorFreeSpanners.cleaning_scale_threshold

#print axioms MinorFreeSpanners.cleaning_scale_nat_loss

#print axioms MinorFreeSpanners.cleaning_dense_scale

#print axioms MinorFreeSpanners.exists_dense_induced_or_small_loss_star_contraction

#print axioms MinorFreeSpanners.IsStarPacking.selected_leaf_degree_ge

#print axioms MinorFreeSpanners.IsStarPacking.induce_selected

#print axioms MinorFreeSpanners.IsStarPacking.regularize_selected_host

#print axioms MinorFreeSpanners.bipartite_cleaning_scale_nat_loss

#print axioms MinorFreeSpanners.exists_bipartite_dense_induced_or_small_loss_contraction

#print axioms MinorFreeSpanners.induced_vertex_deletion_edge_budget

#print axioms MinorFreeSpanners.IsStarPacking.rightMinorModel_bounded

#print axioms MinorFreeSpanners.IsStarPacking.right_quotient_edge_budget

#print axioms MinorFreeSpanners.exists_bipartite_dense_induced_or_right_minor

#print axioms MinorFreeSpanners.bipartite_right_density_gain

#print axioms MinorFreeSpanners.exists_regular_small_star_centers

#print axioms MinorFreeSpanners.exists_regular_bipartite_dense_or_density_minor

#print axioms MinorFreeSpanners.IsStarPacking.regularize_selected_host_integer

#print axioms MinorFreeSpanners.MinorModel.IsBounded.mapHost

#print axioms MinorFreeSpanners.induced_witness_map

#print axioms MinorFreeSpanners.exists_regular_bipartite_dense_or_density_minor_without_unmated

#print axioms MinorFreeSpanners.exists_finite_bounded_dense_minor

#print axioms MinorFreeSpanners.selected_regular_degree_bounds

#print axioms MinorFreeSpanners.selected_bipartite_dense_or_density_minor

#print axioms MinorFreeSpanners.regular_bipartite_density_increment

#print axioms MinorFreeSpanners.bipartite_density_increment

#print axioms MinorFreeSpanners.MinorModel.Covers.comp

#print axioms MinorFreeSpanners.MinorModel.IsFull.comp

#print axioms MinorFreeSpanners.MinorModel.degree_le_branch_sum

#print axioms MinorFreeSpanners.MinorModel.mergeEdge_bounded

#print axioms MinorFreeSpanners.MinorModel.exists_singleton_nonmate

#print axioms MinorFreeSpanners.CleanStarState.step

#print axioms MinorFreeSpanners.clean_star_grow_or_dense

#print axioms MinorFreeSpanners.exists_clean_star_or_dense

#print axioms MinorFreeSpanners.MinorModel.cover_card_eq_sum

#print axioms MinorFreeSpanners.CleanStarState.other_singleton

#print axioms MinorFreeSpanners.CleanStarState.center_adj

#print axioms MinorFreeSpanners.CleanStarState.leaf_card

#print axioms MinorFreeSpanners.exists_minimum_density_induced

#print axioms MinorFreeSpanners.IsGeneralStarForest.fullMinorModel

#print axioms MinorFreeSpanners.IsGeneralStarForest.fullMinorModel_full

#print axioms MinorFreeSpanners.IsGeneralStarForest.quotient_card

#print axioms MinorFreeSpanners.empty_full_star_quotient_edges

#print axioms MinorFreeSpanners.exists_maximum_small_clean_star_forest

#print axioms MinorFreeSpanners.MinorModel.edge_count_le_of_branch_match

#print axioms MinorFreeSpanners.CleanStarState.exists_small_clean_family

#print axioms MinorFreeSpanners.clean_star_or_nonempty_maximum_forest

#print axioms MinorFreeSpanners.CleanStarState.OldBranchInvariant

#print axioms MinorFreeSpanners.CleanStarState.step_preserving

#print axioms MinorFreeSpanners.clean_star_grow_preserving_or_dense

#print axioms MinorFreeSpanners.IsGeneralStarForest.adjoin

#print axioms MinorFreeSpanners.CleanStarState.adjoin_clean_forest

#print axioms MinorFreeSpanners.extend_clean_forest_or_dense

#print axioms MinorFreeSpanners.maximum_clean_forest_residual_bound

#print axioms MinorFreeSpanners.dense_or_maximum_clean_forest_residual

#print axioms MinorFreeSpanners.MinorModel.edge_count_le_of_branch_refinement

#print axioms MinorFreeSpanners.IsGeneralStarForest.restrict

#print axioms MinorFreeSpanners.IsGeneralStarForest.subfamily_edges

#print axioms MinorFreeSpanners.CleanStarState.adjoin_forest_with_loss

#print axioms MinorFreeSpanners.extend_forest_with_loss_or_dense

#print axioms MinorFreeSpanners.IsGeneralStarForest.erased_branch_residual

#print axioms MinorFreeSpanners.replace_one_star_by_two

#print axioms MinorFreeSpanners.maximum_clean_forest_branch_bound

#print axioms MinorFreeSpanners.dense_or_maximum_clean_forest_local_bounds

#print axioms MinorFreeSpanners.exceptionalCoveredVertices_size

#print axioms MinorFreeSpanners.graphCrossingCount_comm

#print axioms MinorFreeSpanners.lowCovered_crossing_budget

#print axioms MinorFreeSpanners.weakResidualVertices_card_bound

#print axioms MinorFreeSpanners.originalLargeVertices_scaled_card

#print axioms MinorFreeSpanners.residualTargetVertices_scaled_card

#print axioms MinorFreeSpanners.residual_bipartite_of_large_residual

#print axioms MinorFreeSpanners.general_clean_coverage_alternative

#print axioms MinorFreeSpanners.exists_densest_induced_core

#print axioms MinorFreeSpanners.edge_count_delete_partition

#print axioms MinorFreeSpanners.incidentEdges_card_bound

#print axioms MinorFreeSpanners.incidentEdges_real_bound

#print axioms MinorFreeSpanners.MinorModel.incident_edge_count_le

#print axioms MinorFreeSpanners.MinorModel.delete_target_edge_budget

#print axioms MinorFreeSpanners.retained_star_quotient_card

#print axioms MinorFreeSpanners.retained_star_quotient_budget

#print axioms MinorFreeSpanners.retained_minor_density_algebra

#print axioms MinorFreeSpanners.residual_loss_coefficient

#print axioms MinorFreeSpanners.clean_coverage_retained_minor_density

#print axioms MinorFreeSpanners.general_density_trichotomy

#print axioms MinorFreeSpanners.induced_density_upper

#print axioms MinorFreeSpanners.exists_densest_core_trichotomy

#print axioms MinorFreeSpanners.general_increment_rounded_degree

#print axioms MinorFreeSpanners.general_increment_imbalance

#print axioms MinorFreeSpanners.real_bipartite_increment

#print axioms MinorFreeSpanners.general_inverse_parameters

#print axioms MinorFreeSpanners.absolute_dense_witness_ratio

#print axioms MinorFreeSpanners.bipartite_density_denominator

#print axioms MinorFreeSpanners.selected_scale_density_increment

#print axioms MinorFreeSpanners.general_graph_density_increment

#print axioms MinorFreeSpanners.sharp_increment_degree

#print axioms MinorFreeSpanners.sharp_increment_factor

#print axioms MinorFreeSpanners.sharp_real_bipartite_increment

#print axioms MinorFreeSpanners.sharp_selected_scale_density_increment

#print axioms MinorFreeSpanners.sharp_general_graph_density_increment

#print axioms MinorFreeSpanners.balanced_density_escalation

#print axioms MinorFreeSpanners.balanced_clique_density_witness

#print axioms MinorFreeSpanners.logarithmic_density_witness

#print axioms MinorFreeSpanners.densityStepWidth_le_log

#print axioms MinorFreeSpanners.densityPolylogLoss_bound

#print axioms MinorFreeSpanners.polylogarithmic_density_witness

#print axioms MinorFreeSpanners.full_density_witness

#print axioms MinorFreeSpanners.fullDensityLoss_polylog

#print axioms MinorFreeSpanners.girth_minor_free_density

#print axioms MinorFreeSpanners.girth_minor_free_edge_bound

#print axioms MinorFreeSpanners.greedy_minor_free_sparsity

#print axioms MinorFreeSpanners.exists_disjoint_neighborhood_packing

#print axioms MinorFreeSpanners.exists_radius_two_clustering

#print axioms MinorFreeSpanners.radius_two_walk_to_center

#print axioms MinorFreeSpanners.exists_high_degree_clustering

#print axioms MinorFreeSpanners.ClusterFamily.lift_walk_supported

#print axioms MinorFreeSpanners.ClusterFamily.merge

#print axioms MinorFreeSpanners.exists_weighted_high_degree_clusters

#print axioms MinorFreeSpanners.high_degree_credit_accounting

#print axioms MinorFreeSpanners.marked_girth_minor_free_edge_bound

#print axioms MinorFreeSpanners.ClusterFamily.marked_edges_card_le

#print axioms MinorFreeSpanners.ClusterFamily.marked_edges_card_le_of_girth

#print axioms MinorFreeSpanners.ClusterFamily.marked_edges_weight_le

#print axioms MinorFreeSpanners.exists_weighted_high_degree_phase

#print axioms MinorFreeSpanners.ConnectedWithin.short_walk

#print axioms MinorFreeSpanners.ConnectedWithin.boundary

#print axioms MinorFreeSpanners.ConnectedWithin.exists_subset_card

#print axioms MinorFreeSpanners.exists_connected_core_packing

#print axioms MinorFreeSpanners.ResidualComponents.connected

#print axioms MinorFreeSpanners.core_residual_boundary

#print axioms MinorFreeSpanners.exists_initial_connected_partition

#print axioms MinorFreeSpanners.ConnectedWithin.induce_connected

#print axioms MinorFreeSpanners.internalEdges_card_lower

#print axioms MinorFreeSpanners.internalEdges_total_le

#print axioms MinorFreeSpanners.unit_short_walk

#print axioms MinorFreeSpanners.exists_initial_unit_clusters

#print axioms MinorFreeSpanners.initial_unit_tree_phase

#print axioms MinorFreeSpanners.branching_neighbor_off_path

#print axioms MinorFreeSpanners.exists_max_mass_path

#print axioms MinorFreeSpanners.ClusterFamily.lift_path_variable

#print axioms MinorFreeSpanners.ConnectedWithin.erase_leaf

#print axioms MinorFreeSpanners.exists_leaf_outside_star

#print axioms MinorFreeSpanners.exists_bounded_branching_core

#print axioms MinorFreeSpanners.exists_branching_core_packing

#print axioms MinorFreeSpanners.exists_weighted_branching_clusters

#print axioms MinorFreeSpanners.branching_reserve_selection

#print axioms MinorFreeSpanners.finite_reserve_payment

#print axioms MinorFreeSpanners.branching_core_credit

#print axioms MinorFreeSpanners.ClusterFamily.crossingEmbedding_not_internal

#print axioms MinorFreeSpanners.ClusterFamily.exists_residual_unit_forest

#print axioms MinorFreeSpanners.ClusterFamily.connectorEdges_total_le

#print axioms MinorFreeSpanners.ClusterFamily.touching_edges_weight_le

#print axioms MinorFreeSpanners.exists_weighted_branching_phase

#print axioms MinorFreeSpanners.branching_phase_conservation

#print axioms MinorFreeSpanners.connected_forest_degree_two_path

#print axioms MinorFreeSpanners.exists_weighted_path_prefix

#print axioms MinorFreeSpanners.WeightedPathArms.mass

#print axioms MinorFreeSpanners.WeightedPathArms.radial_path

#print axioms MinorFreeSpanners.exists_weighted_path_arms

#print axioms MinorFreeSpanners.four_arm_credit

#print axioms MinorFreeSpanners.rooted_sets_bridge

#print axioms MinorFreeSpanners.ClusterFamily.arm_to_center

#print axioms MinorFreeSpanners.ClusterFamily.four_arm_walks

#print axioms MinorFreeSpanners.ClusterFamily.four_arm_core_of_paths

#print axioms MinorFreeSpanners.ClusterFamily.FourArmCore.credit

#print axioms MinorFreeSpanners.ClusterFamily.exists_four_arm_packing

#print axioms MinorFreeSpanners.ClusterFamily.no_residual_four_arm_edge

#print axioms MinorFreeSpanners.exists_weighted_four_arm_phase

#print axioms MinorFreeSpanners.pathMass_append

#print axioms MinorFreeSpanners.exists_balanced_path_split

#print axioms MinorFreeSpanners.bounded_surplus_payment

#print axioms MinorFreeSpanners.ClusterFamily.coarse_path_detour_gap

#print axioms MinorFreeSpanners.ClusterFamily.path_to_start

#print axioms MinorFreeSpanners.ClusterFamily.short_cycle_walks

#print axioms MinorFreeSpanners.ShortCycleArms.mass_exact

#print axioms MinorFreeSpanners.ShortCycleArms.credit_gap

#print axioms MinorFreeSpanners.ClusterFamily.short_cycle_paid_core

#print axioms MinorFreeSpanners.exists_short_cycle_arms

#print axioms MinorFreeSpanners.ClusterFamily.short_cycle_core_of_paths

#print axioms MinorFreeSpanners.ClusterFamily.ShortCycleCore.paid

#print axioms MinorFreeSpanners.ClusterFamily.exists_short_cycle_packing

#print axioms MinorFreeSpanners.exists_weighted_short_cycle_phase

#print axioms MinorFreeSpanners.separated_path_supports

#print axioms MinorFreeSpanners.exists_separated_path_pieces

#print axioms MinorFreeSpanners.exists_weighted_joined_arms

#print axioms MinorFreeSpanners.ClusterFamily.same_path_core_dichotomy

#print axioms MinorFreeSpanners.ClusterFamily.exists_path_core_partition

#print axioms MinorFreeSpanners.ClusterFamily.residual_same_path_edge_near_end

#print axioms MinorFreeSpanners.ClusterFamily.residual_distinct_paths_edge_near_end

#print axioms MinorFreeSpanners.residual_component_boundary

#print axioms MinorFreeSpanners.exists_residual_component_owners

#print axioms MinorFreeSpanners.exists_max_supported_path

#print axioms MinorFreeSpanners.path_mass_bound_through_root

#print axioms MinorFreeSpanners.exists_rooted_diameter_path

#print axioms MinorFreeSpanners.rooted_absorption_reserve

#print axioms MinorFreeSpanners.finite_external_reserve_payment

#print axioms MinorFreeSpanners.rooted_absorption_payment

#print axioms MinorFreeSpanners.root_avoiding_transfer

#print axioms MinorFreeSpanners.root_avoiding_component_bound

#print axioms MinorFreeSpanners.rooted_residual_connected

#print axioms MinorFreeSpanners.components_reach_chosen_ports

#print axioms MinorFreeSpanners.owned_component_absorption

#print axioms MinorFreeSpanners.weighted_rooted_absorption

#print axioms MinorFreeSpanners.exists_residual_ownership

#print axioms MinorFreeSpanners.ResidualOwnership.filled_disjoint

#print axioms MinorFreeSpanners.ResidualOwnership.filled_covers

#print axioms MinorFreeSpanners.exists_small_component_absorption_phase

#print axioms MinorFreeSpanners.ClusterFamily.selectedResidual

#print axioms MinorFreeSpanners.ClusterFamily.selectedResidual_covers

#print axioms MinorFreeSpanners.ClusterFamily.selectedResidual_intrinsic

#print axioms MinorFreeSpanners.ClusterFamily.graph_connected_of_cover

#print axioms MinorFreeSpanners.originalResidualIndices_card

#print axioms MinorFreeSpanners.ClusterFamily.mixed_residual_heavy_edges

#print axioms MinorFreeSpanners.exists_mixed_small_absorption_phase

#print axioms MinorFreeSpanners.exists_weighted_disjoint_path_split

#print axioms MinorFreeSpanners.exists_weighted_path_partition

#print axioms MinorFreeSpanners.exists_weighted_path_block_family

#print axioms MinorFreeSpanners.disjoint_path_block_port

#print axioms MinorFreeSpanners.endpoint_blocks_card

#print axioms MinorFreeSpanners.exists_attached_path_blocks

#print axioms MinorFreeSpanners.root_avoiding_component_cover

#print axioms MinorFreeSpanners.from_root_component_cover

#print axioms MinorFreeSpanners.simple_path_two_component_cover

#print axioms MinorFreeSpanners.rooted_absorption_path_reserve

#print axioms MinorFreeSpanners.rooted_reserve_two_components

#print axioms MinorFreeSpanners.path_released_credit_lower

#print axioms MinorFreeSpanners.residual_path_donor_credit

#print axioms MinorFreeSpanners.finite_two_exception_charge

#print axioms MinorFreeSpanners.rooted_long_donor_payment

#print axioms MinorFreeSpanners.weighted_donor_absorption
