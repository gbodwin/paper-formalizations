import DirectedFlowCutGap.ActualPackingStart
import DirectedFlowCutGap.PackingGraphContext
import DirectedFlowCutGap.PackingStartBounds
import DirectedFlowCutGap.PackingStartCalls
import DirectedFlowCutGap.PackingStartExecution
import DirectedFlowCutGap.PackingStartFinalAllocation
import DirectedFlowCutGap.PackingStartGraphCalls
import DirectedFlowCutGap.PackingStartInitialOracle
import DirectedFlowCutGap.PackingStartInput
import DirectedFlowCutGap.PackingStartNormalizeState
import DirectedFlowCutGap.PackingStartProgram
import DirectedFlowCutGap.PackingStateRecord
import DirectedFlowCutGap.PackingZeroRowConstruction
import DirectedFlowCutGap.PackingZeroRowProgram
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "PACKING_START_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualPackingStart,`DirectedFlowCutGap.PackingGraphContext,`DirectedFlowCutGap.PackingStartBounds,`DirectedFlowCutGap.PackingStartCalls,`DirectedFlowCutGap.PackingStartExecution,`DirectedFlowCutGap.PackingStartFinalAllocation,`DirectedFlowCutGap.PackingStartGraphCalls,`DirectedFlowCutGap.PackingStartInitialOracle,`DirectedFlowCutGap.PackingStartInput,`DirectedFlowCutGap.PackingStartNormalizeState,`DirectedFlowCutGap.PackingStartProgram,`DirectedFlowCutGap.PackingStateRecord,`DirectedFlowCutGap.PackingZeroRowConstruction,`DirectedFlowCutGap.PackingZeroRowProgram]
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
    logInfo m!"PACKING_START_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"PACKING_START_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.PackingGraphContext.construct_return,`DirectedFlowCutGap.PackingZeroRow.replicate_return,`DirectedFlowCutGap.PackingZeroRow.zero_packed,`DirectedFlowCutGap.PackingStart.call_run,`DirectedFlowCutGap.PackingStart.initial_oracle,`DirectedFlowCutGap.PackingStart.normalize_state,`DirectedFlowCutGap.PackingStart.start_high,`DirectedFlowCutGap.PackingStart.start_steps_bound,`DirectedFlowCutGap.PackingStart.start_bit] do
    IO.eprintln s!"PACKING_START_CLOSURE_BEGIN {root}"
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
    logInfo m!"PACKING_START_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
