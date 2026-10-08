import VFTSpanners
import LinearDistancePreservers
import Lean.Util.CollectAxioms

/-! Audit all declarations by defining module, including private/generated
ones and declarations whose namespace differs from their defining module. -/
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for root in #[`VFTSpanners, `LinearDistancePreservers] do
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
