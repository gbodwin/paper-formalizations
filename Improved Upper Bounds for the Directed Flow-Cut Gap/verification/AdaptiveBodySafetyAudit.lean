import DirectedFlowCutGap.AdaptivePackingAmountState
import DirectedFlowCutGap.AdaptivePackingArithmeticCalls
import DirectedFlowCutGap.AdaptivePackingBestState
import DirectedFlowCutGap.AdaptivePackingCallLift
import DirectedFlowCutGap.AdaptivePackingChoiceState
import DirectedFlowCutGap.AdaptivePackingContextState
import DirectedFlowCutGap.AdaptivePackingFieldPath
import DirectedFlowCutGap.AdaptivePackingGraphCalls
import DirectedFlowCutGap.AdaptivePackingGuardCall
import DirectedFlowCutGap.AdaptivePackingNormalizedState
import DirectedFlowCutGap.AdaptivePackingObjectiveState
import DirectedFlowCutGap.AdaptivePackingOracleState
import DirectedFlowCutGap.AdaptivePackingScalarCalls
import DirectedFlowCutGap.AdaptivePackingStateOutput
import DirectedFlowCutGap.AdaptivePackingStateProgram
import DirectedFlowCutGap.AdaptivePackingUpdateCalls
import DirectedFlowCutGap.AdaptivePackingUpdateHandover
import DirectedFlowCutGap.AdaptivePackingWeightInput
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "ADAPTIVE_BODY_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.AdaptivePackingAmountState,`DirectedFlowCutGap.AdaptivePackingArithmeticCalls,`DirectedFlowCutGap.AdaptivePackingBestState,`DirectedFlowCutGap.AdaptivePackingCallLift,`DirectedFlowCutGap.AdaptivePackingChoiceState,`DirectedFlowCutGap.AdaptivePackingContextState,`DirectedFlowCutGap.AdaptivePackingFieldPath,`DirectedFlowCutGap.AdaptivePackingGraphCalls,`DirectedFlowCutGap.AdaptivePackingGuardCall,`DirectedFlowCutGap.AdaptivePackingNormalizedState,`DirectedFlowCutGap.AdaptivePackingObjectiveState,`DirectedFlowCutGap.AdaptivePackingOracleState,`DirectedFlowCutGap.AdaptivePackingScalarCalls,`DirectedFlowCutGap.AdaptivePackingStateOutput,`DirectedFlowCutGap.AdaptivePackingStateProgram,`DirectedFlowCutGap.AdaptivePackingUpdateCalls,`DirectedFlowCutGap.AdaptivePackingUpdateHandover,`DirectedFlowCutGap.AdaptivePackingWeightInput]
  let wantedSet : NameSet := wanted.foldl (fun seen name => seen.insert name) {}
  let mut counts : NameMap Nat := {}
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := modules[idx.toNat]!
      if wantedSet.contains module then
        counts := counts.insert module ((counts.find? module).getD 0+1)
        count := count+1
        if ci.isUnsafe then throwError "Unsafe oracle component declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden oracle component axiom: {name}: {ax}"
  for module in wanted do
    let found := (counts.find? module).getD 0
    if found == 0 then throwError "No declarations audited for {module}"
    logInfo m!"ADAPTIVE_BODY_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"ADAPTIVE_BODY_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.AdaptivePackingState.stopped_high,`DirectedFlowCutGap.AdaptivePackingState.actual_choice_prefix,`DirectedFlowCutGap.AdaptivePackingState.actual_amount_handover,`DirectedFlowCutGap.AdaptivePackingState.actual_normalized_handover,`DirectedFlowCutGap.AdaptivePackingState.actual_objective_handover,`DirectedFlowCutGap.AdaptivePackingState.actual_best_handover,`DirectedFlowCutGap.AdaptivePackingState.prepare_weights,`DirectedFlowCutGap.AdaptivePackingState.prepare_total,`DirectedFlowCutGap.AdaptivePackingState.prepare_loads,`DirectedFlowCutGap.AdaptivePackingState.allocate_state] do
    IO.eprintln s!"ADAPTIVE_BODY_CLOSURE_BEGIN {root}"
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut axioms : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      unless seen.contains name do
        seen := seen.insert name
        let some ci := env.find? name | throwError "Missing closure constant: {name}"
        if ci.isUnsafe then throwError "Unsafe closure constant: {root}: {name}"
        match ci with
        | .axiomInfo _ =>
          axioms := axioms.insert name
          unless allowed.contains name do throwError "Forbidden closure axiom: {root}: {name}"
        | _ => pure ()
        for dep in ci.getUsedConstantsAsSet.toList do
          unless seen.contains dep do todo := todo.push dep
    logInfo m!"ADAPTIVE_BODY_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
