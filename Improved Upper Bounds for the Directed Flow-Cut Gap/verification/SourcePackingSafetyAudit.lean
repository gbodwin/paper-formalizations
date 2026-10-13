import DirectedFlowCutGap.ActualSourcePacking
import DirectedFlowCutGap.SourcePackingBoundMonotonicity
import DirectedFlowCutGap.SourcePackingCallLift
import DirectedFlowCutGap.SourcePackingEncoding
import DirectedFlowCutGap.SourcePackingExecution
import DirectedFlowCutGap.SourcePackingInputLength
import DirectedFlowCutGap.SourcePackingLengthExecution
import DirectedFlowCutGap.SourcePackingProgram
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "SOURCE_SOLVER_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualSourcePacking,`DirectedFlowCutGap.SourcePackingBoundMonotonicity,`DirectedFlowCutGap.SourcePackingCallLift,`DirectedFlowCutGap.SourcePackingEncoding,`DirectedFlowCutGap.SourcePackingExecution,`DirectedFlowCutGap.SourcePackingInputLength,`DirectedFlowCutGap.SourcePackingLengthExecution,`DirectedFlowCutGap.SourcePackingProgram]
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
    logInfo m!"SOURCE_SOLVER_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"SOURCE_SOLVER_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.SourcePacking.input_slots,`DirectedFlowCutGap.SourcePacking.run_slots,`DirectedFlowCutGap.SourcePacking.fields_width,`DirectedFlowCutGap.SourcePacking.solve_source,`DirectedFlowCutGap.SourcePacking.solve_source_bit,`DirectedFlowCutGap.SourcePackingBound.mono_EnumeratedPacking_instructionBound,`DirectedFlowCutGap.SourcePacking.table_encode_length,`DirectedFlowCutGap.SourcePacking.input_metrics,`DirectedFlowCutGap.SourcePacking.source_bound,`DirectedFlowCutGap.SourcePacking.solve_source_length_bit] do
    IO.eprintln s!"SOURCE_SOLVER_CLOSURE_BEGIN {root}"
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
    logInfo m!"SOURCE_SOLVER_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
