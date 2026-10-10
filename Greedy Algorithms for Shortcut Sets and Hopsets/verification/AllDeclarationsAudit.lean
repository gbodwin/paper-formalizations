import GreedyShortcuts
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let ours := match env.getModuleIdxFor? name with
      | some idx => match modules[idx.toNat]? with
        | some moduleName => (`GreedyShortcuts).isPrefixOf moduleName
        | none => false
      | none => false
    if ours then
      count := count + 1
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then
    throwError "No GreedyShortcuts declarations were audited"
  logInfo m!"Audited {count} GreedyShortcuts declarations; only {allowed}"

#print axioms GreedyShortcuts.RecapArithmetic.rounds_bound
#print axioms GreedyShortcuts.FinitePotential.zero_after_blocks

#print axioms GreedyShortcuts.FiniteGreedy.System.run_terminates
#print axioms GreedyShortcuts.FiniteGreedy.System.final_card_of_relative_progress

#print axioms GreedyShortcuts.DirectedPaths.reachable_augment_iff
#print axioms GreedyShortcuts.GraphGreedy.output_hop_bound
#print axioms GreedyShortcuts.ShortcutWalk.repairEdges_repair

#print axioms GreedyShortcuts.WarmupUnweighted.output_card_bound

#print axioms GreedyShortcuts.CanonicalSegments.intersection_convex
#print axioms GreedyShortcuts.WarmupBound.output_card_bound_all
#print axioms GreedyShortcuts.FiniteWindows.exists_high_score

#print axioms GreedyShortcuts.WeightedPaths.exists_unique_minhop_reweighting
#print axioms GreedyShortcuts.WeightedPaths.distance_augment

#print axioms GreedyShortcuts.WeightedGreedy.output_hop_bound
#print axioms GreedyShortcuts.WeightedGreedy.output_distance
#print axioms GreedyShortcuts.FamilyWindows.exists_window
#print axioms GreedyShortcuts.FiniteHorizon.output_card_before

#print axioms GreedyShortcuts.WeightedPaths.hop_after_subwalk_state
#print axioms GreedyShortcuts.WarmupWeighted.output_card_bound_all

#print axioms GreedyShortcuts.WeightedPaths.multi_edge_savings
#print axioms GreedyShortcuts.WeightedPaths.CompatibleReweighting.hop_augment_le
#print axioms GreedyShortcuts.WeightedStateProgress.state_progress
#print axioms GreedyShortcuts.WeightedBenchmark.directed_near_existential

#print axioms GreedyShortcuts.WeightedBenchmark.directed_logarithmic_budget
#print axioms GreedyShortcuts.WeightedPaths.exists_symmetric_minhop_reweighting
#print axioms GreedyShortcuts.Undirected.potential_eq_twice_unordered
#print axioms GreedyShortcuts.Undirected.state_progress
#print axioms GreedyShortcuts.UndirectedBenchmark.undirected_near_existential

#print axioms GreedyShortcuts.SuffixWindowPath.exists_suffix_window
#print axioms GreedyShortcuts.CanonicalSuffixPath.exists_current_high_score_path

#print axioms GreedyShortcuts.SuffixIncidence.degree_sum_intersections
#print axioms GreedyShortcuts.SuffixIntersections.indices_convex
#print axioms GreedyShortcuts.CanonicalSavings.common_shortcut_saving
#print axioms GreedyShortcuts.HeavyCharging.heavy_relative

#print axioms GreedyShortcuts.LightCharging.common_prefix_progress
#print axioms GreedyShortcuts.LightCharging.light_relative
#print axioms GreedyShortcuts.DAGProgress.local_dichotomy
#print axioms GreedyShortcuts.DAGProgress.output_card_bound

#print axioms GreedyShortcuts.DAGBalance.output_card_log_bound

#print axioms GreedyShortcuts.DAGAllTargets.output_card_log_bound
#print axioms GreedyShortcuts.ChainUnion.supershortcut_union
#print axioms GreedyShortcuts.NormalizedReachability.reachable_filtered_iff
#print axioms GreedyShortcuts.NormalizedValidity.color_convex
#print axioms GreedyShortcuts.ChainNormalization.valid_paths_exist

#print axioms GreedyShortcuts.ChainDistance.Context.distance_antitone
#print axioms GreedyShortcuts.FiniteThresholdGreedy.System.run_terminates
#print axioms GreedyShortcuts.ChainDistance.Context.progress
#print axioms GreedyShortcuts.ChainDistance.Context.output_correct
#print axioms GreedyShortcuts.ChainDistance.Context.distance_valid_minimizer

#print axioms GreedyShortcuts.SCCQuotient.acyclic
#print axioms GreedyShortcuts.SCCQuotient.lifted_hop_bound
#print axioms GreedyShortcuts.SCCGreedy.output_card_log_bound
#print axioms GreedyShortcuts.SCCGreedy.target_hop_bound

#print axioms GreedyShortcuts.KernelLift.identityKernel
#print axioms GreedyShortcuts.KernelLift.Kernel.output_hop_bound
#print axioms GreedyShortcuts.KernelLift.Kernel.output_card_log_bound

#print axioms GreedyShortcuts.ChainDistance.Context.first_inherits
#print axioms GreedyShortcuts.ChainDistance.Context.subwalk_valid

#print axioms GreedyShortcuts.ChainCover.uncovered_le_of_legal
#print axioms GreedyShortcuts.ColoredHopBound.compress
#print axioms GreedyShortcuts.ChainDistance.Context.shortcuts_hop_bound

#print axioms GreedyShortcuts.KernelBalance.output_card
#print axioms GreedyShortcuts.KernelBalance.output_hop_scaled

#print axioms GreedyShortcuts.KernelTarget.output_hop
#print axioms GreedyShortcuts.KernelTarget.output_card

#print axioms GreedyShortcuts.SCCBudget.target_card_scaled
#print axioms GreedyShortcuts.SCCBudget.small_target_card_scaled

#print axioms GreedyShortcuts.ChainDistance.Context.distance_guard_dichotomy

#print axioms GreedyShortcuts.FiniteHitting.output_card
#print axioms GreedyShortcuts.KernelSamples.sampleKernel
#print axioms GreedyShortcuts.KernelSamples.samples_card_le

#print axioms GreedyShortcuts.GeneralDirected.output_card
#print axioms GreedyShortcuts.GeneralDirected.output_hop

#print axioms GreedyShortcuts.GeneralIntegerBound.output_card
#print axioms GreedyShortcuts.GeneralPowerBound.output_card_log

#print axioms GreedyShortcuts.ChainDistance.Context.minimum_prefix
#print axioms GreedyShortcuts.ChainDistance.Context.pathEntries_card
#print axioms GreedyShortcuts.ChainDistance.Context.minimum_takeUntil

#print axioms GreedyShortcuts.ChainDistance.Context.prefix_candidate
#print axioms GreedyShortcuts.ChainDistance.Context.one_source_product_drop
#print axioms GreedyShortcuts.ChainDistance.Context.exists_important_prefix_count
#print axioms GreedyShortcuts.ChainDistance.Context.exists_quadratic_drop_for_pair
#print axioms GreedyShortcuts.FiniteThresholdGreedy.System.final_card_of_relative_blocks
#print axioms GreedyShortcuts.ChainDistance.Context.step_relative_progress
#print axioms GreedyShortcuts.ChainDistance.Context.output_card_quadratic
#print axioms GreedyShortcuts.ChainDistance.Context.quadratic_shortcuts_spec
#print axioms GreedyShortcuts.ChainDistance.Context.quadratic_scaled_output
#print axioms GreedyShortcuts.FinitePotential.reciprocal_decay
#print axioms GreedyShortcuts.FinitePotential.zero_after_quadratic
#print axioms GreedyShortcuts.ChainDistance.Context.step_squared_bounds
#print axioms GreedyShortcuts.ChainDistance.Context.output_card_quadratic_sharp
#print axioms GreedyShortcuts.ChainDistance.Context.quadratic_scaled_output_sharp
#print axioms GreedyShortcuts.UniformChainPacking.packing_card_mul
#print axioms GreedyShortcuts.UniformChainPacking.outside_path_lt
#print axioms GreedyShortcuts.UniformChainPacking.context_cover
#print axioms GreedyShortcuts.UniformChainPacking.packedOutput_spec
#print axioms GreedyShortcuts.UniformChainPacking.defaultOutput_spec
#print axioms GreedyShortcuts.ChainDistance.Context.interior_insertion_saving
#print axioms GreedyShortcuts.ChainDistance.Context.rectangle_insertion_drop
#print axioms GreedyShortcuts.ChainDistance.Context.guard_shared_chains
#print axioms GreedyShortcuts.ChainDistance.Context.guard_offpath_entries
#print axioms GreedyShortcuts.ChainDistance.Context.exists_guard_offpath_supply
#print axioms GreedyShortcuts.ChainDistance.Context.guard_cone_depletion

#print axioms GreedyShortcuts.FiniteGuardDescent.exists_good
#print axioms GreedyShortcuts.ChainDistance.Context.exists_stable_window_target
#print axioms GreedyShortcuts.ChainDistance.Context.exists_entry_level
#print axioms GreedyShortcuts.ChainDistance.Context.insertion_route_bound
#print axioms GreedyShortcuts.ChainDistance.Context.stable_path_rectangle
#print axioms GreedyShortcuts.ChainDistance.Context.exists_window_drop_for_pair
#print axioms GreedyShortcuts.ChainDistance.Context.exists_sixth_power_drop_for_pair
#print axioms GreedyShortcuts.ChainDistance.Context.step_window_drop

#print axioms GreedyShortcuts.PathMedian.edges_card
#print axioms GreedyShortcuts.PathMedian.two_legs
#print axioms GreedyShortcuts.PathMedian.finEdges_short
#print axioms GreedyShortcuts.PathMedian.supershortcut_union
