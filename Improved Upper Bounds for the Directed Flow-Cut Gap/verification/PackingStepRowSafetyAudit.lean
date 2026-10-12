import DirectedFlowCutGap.ActualPackingEntry
import DirectedFlowCutGap.ActualPackingGuard
import DirectedFlowCutGap.ActualPackingUpdateRow
import DirectedFlowCutGap.PackingEntryBounds
import DirectedFlowCutGap.PackingEntryCalls
import DirectedFlowCutGap.PackingEntryConstants
import DirectedFlowCutGap.PackingEntryExecution
import DirectedFlowCutGap.PackingEntryProgram
import DirectedFlowCutGap.PackingGuardBounds
import DirectedFlowCutGap.PackingGuardComparison
import DirectedFlowCutGap.PackingGuardExecution
import DirectedFlowCutGap.PackingGuardProgram
import DirectedFlowCutGap.PackingGuardState
import DirectedFlowCutGap.PackingUpdateEntryCall
import DirectedFlowCutGap.PackingUpdateRowBounds
import DirectedFlowCutGap.PackingUpdateRowHead
import DirectedFlowCutGap.PackingUpdateRowProgram
import DirectedFlowCutGap.PackingUpdateRowRefinement
import DirectedFlowCutGap.PackingUpdateRowTail
import DirectedFlowCutGap.PackingUpdateRowTrace
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "PACKING_STEP_ROW_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualPackingEntry,`DirectedFlowCutGap.ActualPackingGuard,`DirectedFlowCutGap.ActualPackingUpdateRow,`DirectedFlowCutGap.PackingEntryBounds,`DirectedFlowCutGap.PackingEntryCalls,`DirectedFlowCutGap.PackingEntryConstants,`DirectedFlowCutGap.PackingEntryExecution,`DirectedFlowCutGap.PackingEntryProgram,`DirectedFlowCutGap.PackingGuardBounds,`DirectedFlowCutGap.PackingGuardComparison,`DirectedFlowCutGap.PackingGuardExecution,`DirectedFlowCutGap.PackingGuardProgram,`DirectedFlowCutGap.PackingGuardState,`DirectedFlowCutGap.PackingUpdateEntryCall,`DirectedFlowCutGap.PackingUpdateRowBounds,`DirectedFlowCutGap.PackingUpdateRowHead,`DirectedFlowCutGap.PackingUpdateRowProgram,`DirectedFlowCutGap.PackingUpdateRowRefinement,`DirectedFlowCutGap.PackingUpdateRowTail,`DirectedFlowCutGap.PackingUpdateRowTrace]
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
    logInfo m!"PACKING_STEP_ROW_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"PACKING_STEP_ROW_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.PackingGuard.guard_high,`DirectedFlowCutGap.PackingGuard.state_guard,`DirectedFlowCutGap.PackingGuard.steps_bound,`DirectedFlowCutGap.PackingGuard.guard_bit,`DirectedFlowCutGap.PackingEntry.constants_run,`DirectedFlowCutGap.PackingEntry.entry_high,`DirectedFlowCutGap.PackingEntry.steps_bound,`DirectedFlowCutGap.PackingEntry.result_eq_update,`DirectedFlowCutGap.PackingEntry.entry_bit,`DirectedFlowCutGap.PackingUpdateRow.row_return,`DirectedFlowCutGap.PackingUpdateRow.result_eq_update,`DirectedFlowCutGap.PackingUpdateRow.steps_bound,`DirectedFlowCutGap.PackingUpdateRow.result_width,`DirectedFlowCutGap.PackingUpdateRow.row_bit] do
    IO.eprintln s!"PACKING_STEP_ROW_CLOSURE_BEGIN {root}"
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
    logInfo m!"PACKING_STEP_ROW_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
