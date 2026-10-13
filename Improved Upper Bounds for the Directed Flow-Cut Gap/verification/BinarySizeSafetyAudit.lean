import DirectedFlowCutGap.ActualBinarySize
import DirectedFlowCutGap.BinarySizeCallLift
import DirectedFlowCutGap.BinarySizeCalls
import DirectedFlowCutGap.BinarySizeExecution
import DirectedFlowCutGap.BinarySizeProgram
import DirectedFlowCutGap.BinarySizeTrace
import DirectedFlowCutGap.BinarySizeValue
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "BINARY_SIZE_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualBinarySize, `DirectedFlowCutGap.BinarySizeCallLift, `DirectedFlowCutGap.BinarySizeCalls, `DirectedFlowCutGap.BinarySizeExecution, `DirectedFlowCutGap.BinarySizeProgram, `DirectedFlowCutGap.BinarySizeTrace, `DirectedFlowCutGap.BinarySizeValue]
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
    logInfo m!"BINARY_SIZE_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"BINARY_SIZE_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.BinarySizeProgram.program, `DirectedFlowCutGap.BinarySizeProgram.countWord_succ, `DirectedFlowCutGap.BinarySizeProgram.countWord_exact, `DirectedFlowCutGap.BinarySizeProgram.trim_call, `DirectedFlowCutGap.BinarySizeProgram.length_call, `DirectedFlowCutGap.BinarySizeProgram.size_return, `DirectedFlowCutGap.BinarySizeProgram.steps_bound, `DirectedFlowCutGap.BinarySizeProgram.size, `DirectedFlowCutGap.BinarySizeProgram.size_bit] do
    IO.eprintln s!"BINARY_SIZE_CLOSURE_BEGIN {root}"
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
    logInfo m!"BINARY_SIZE_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
