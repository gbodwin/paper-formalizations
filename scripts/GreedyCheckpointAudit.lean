import GreedyShortcuts.ChainStrictJoinGuardV2
import GreedyShortcuts.ChainSharedPivotGuardV2
import GreedyShortcuts.ChainCertifiedRootProjection
import GreedyShortcuts.ChainSharedPivotRootProjectionV2
import GreedyShortcuts.ChainGuardCone
import GreedyShortcuts.ChainProjectedConeOwners
import GreedyShortcuts.ChainPrefixSavings
import GreedyShortcuts.ChainMaximumChildSelector
import GreedyShortcuts.ChainOwnerLastRootTail
import GreedyShortcuts.ChainFixedRootSuffix
import GreedyShortcuts.ChainCoalescingRootSuffix
import GreedyShortcuts.ChainRootTailHeadOrder
import GreedyShortcuts.ChainSuffixCharging
import GreedyShortcuts.ChainLevels
import GreedyShortcuts.ChainEntryLevels
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env ← getEnv
  -- Lazy equation theorems can be exported by multiple modules. Import order
  -- chooses their defining-module attribution, not their type/proof/axioms.
  -- Counts below describe the stable declarations; this required theorem is
  -- still included in the unfiltered, complete axiom-audit loop below.
  let shared := `GreedyShortcuts.ChainDistance.Context.count.eq_1
  let some sharedInfo := env.find? shared
    | throwError "Missing required shared generated declaration {shared}"
  match sharedInfo with
  | .thmInfo _ => pure ()
  | _ => throwError "Required shared generated declaration is not a theorem: {shared}"
  let some sharedIdx := env.getModuleIdxFor? shared
    | throwError "Missing defining module for {shared}"
  let sharedOwner := env.allImportedModuleNames[sharedIdx.toNat]!
  unless sharedOwner == `GreedyShortcuts.ChainStrictJoinGuardV2 ||
      sharedOwner == `GreedyShortcuts.ChainEntryLevels do
    throwError "Unexpected defining module {sharedOwner} for {shared}"
  logInfo m!"CHECKPOINT_SHARED_GENERATED {shared} OWNER {sharedOwner}"
  for (moduleName, expected) in #[(`GreedyShortcuts.ChainStrictJoinGuardV2, 9),
                                  (`GreedyShortcuts.ChainSharedPivotGuardV2, 3),
                                  (`GreedyShortcuts.ChainCertifiedRootProjection, 5),
                                  (`GreedyShortcuts.ChainSharedPivotRootProjectionV2, 1),
                                  (`GreedyShortcuts.ChainGuardCone, 9),
                                  (`GreedyShortcuts.ChainProjectedConeOwners, 7),
                                  (`GreedyShortcuts.ChainPrefixSavings, 9),
                                  (`GreedyShortcuts.ChainMaximumChildSelector, 9),
                                  (`GreedyShortcuts.ChainOwnerLastRootTail, 44),
                                  (`GreedyShortcuts.ChainFixedRootSuffix, 15),
                                  (`GreedyShortcuts.ChainCoalescingRootSuffix, 25),
                                  (`GreedyShortcuts.ChainRootTailHeadOrder, 24),
                                  (`GreedyShortcuts.ChainSuffixCharging, 5),
                                  (`GreedyShortcuts.ChainLevels, 18),
                                  (`GreedyShortcuts.ChainEntryLevels, 12)] do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing checkpoint module {moduleName}"
    let decls := env.constants.toList.filter (fun x => env.getModuleIdxFor? x.1 == some idx)
    let stableDecls := decls.filter (fun x => x.1 != shared)
    let requiredNames : Array String :=
      if moduleName == `GreedyShortcuts.ChainStrictJoinGuardV2 then
        #["GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._proof_1_6",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._proof_1_7",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._proof_1_8",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._simp_1_2",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._simp_1_4",
          "GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2._simp_1_5",
          "_private.GreedyShortcuts.ChainStrictJoinGuardV2.0.GreedyShortcuts.ChainDistance.Context.strictJoinV2_last_rejected_split"]
      else if moduleName == `GreedyShortcuts.ChainEntryLevels then
        #["GreedyShortcuts.ChainDistance.Context.count_take_mono",
          "GreedyShortcuts.ChainDistance.Context.count_take_zero_le",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_1",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_3",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_4",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_5",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_6",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_7",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_8",
          "GreedyShortcuts.ChainDistance.Context.exists_entry_level._proof_1_9",
          "GreedyShortcuts.ChainDistance.Context.minimum_take"]
      else #[]
    for required in requiredNames do
      unless stableDecls.any (fun x => x.1.toString == required) do
        throwError "Missing required checkpoint declaration {required} from {moduleName}"
    unless stableDecls.length == expected do
      throwError "Unexpected stable declaration coverage for {moduleName}: {stableDecls.length}"
    for (name, info) in decls do
      if info.isAxiom then throwError "Declared axiom {name}"
      let axioms ← collectAxioms name
      logInfo m!"CHECKPOINT_DECL {name} AXIOMS {axioms}"
      for ax in axioms do
        unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"CHECKPOINT_MODULE {moduleName} DECLARATIONS {decls.length} STABLE_DECLARATIONS {stableDecls.length}"

#print axioms GreedyShortcuts.ChainDistance.Context.strict_join_last_guard_offpath_v2
#print axioms GreedyShortcuts.ChainDistance.Context.selected_pivot_suffix_prices_v2
#print axioms GreedyShortcuts.ChainDistance.Context.selected_shared_pivot_last_guard_offpath_v2
