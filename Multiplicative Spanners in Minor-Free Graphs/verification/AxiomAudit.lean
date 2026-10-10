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
