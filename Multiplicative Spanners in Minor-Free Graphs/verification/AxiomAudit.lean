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
