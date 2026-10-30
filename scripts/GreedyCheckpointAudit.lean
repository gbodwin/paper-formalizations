import GreedyShortcuts.ChainStrictJoinGuardV2
import GreedyShortcuts.ChainSharedPivotGuardV2
import GreedyShortcuts.ChainCertifiedRootProjection
import GreedyShortcuts.ChainSharedPivotRootProjectionV2
import GreedyShortcuts.ChainGuardCone
import GreedyShortcuts.ChainProjectedConeOwners
import GreedyShortcuts.ChainPrefixSavings
import GreedyShortcuts.ChainMaximumChildSelector
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (moduleName, expected) in #[(`GreedyShortcuts.ChainStrictJoinGuardV2, 10),
                                  (`GreedyShortcuts.ChainSharedPivotGuardV2, 3),
                                  (`GreedyShortcuts.ChainCertifiedRootProjection, 5),
                                  (`GreedyShortcuts.ChainSharedPivotRootProjectionV2, 1),
                                  (`GreedyShortcuts.ChainGuardCone, 9),
                                  (`GreedyShortcuts.ChainProjectedConeOwners, 7),
                                  (`GreedyShortcuts.ChainPrefixSavings, 9),
                                  (`GreedyShortcuts.ChainMaximumChildSelector, 9)] do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing checkpoint module {moduleName}"
    let decls := env.constants.toList.filter (fun x => env.getModuleIdxFor? x.1 == some idx)
    unless decls.length == expected do
      throwError "Unexpected declaration coverage for {moduleName}: {decls.length}"
    for (name, info) in decls do
      if info.isAxiom then throwError "Declared axiom {name}"
      let axioms ← collectAxioms name
      logInfo m!"CHECKPOINT_DECL {name} AXIOMS {axioms}"
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"CHECKPOINT_MODULE {moduleName} DECLARATIONS {decls.length}"

#print axioms GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2
#print axioms GreedyShortcuts.ChainDistance.Context.selected_pivot_suffix_prices_v2
#print axioms GreedyShortcuts.ChainDistance.Context.selected_shared_pivot_last_guard_offpath_v2
