import DirectedFlowCutGap.ActualGridFamily
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "GRID_FAMILY_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualGridFamily, `DirectedFlowCutGap.GridFamilyAdvance, `DirectedFlowCutGap.GridFamilyCallLift, `DirectedFlowCutGap.GridFamilyControlCalls, `DirectedFlowCutGap.GridFamilyData, `DirectedFlowCutGap.GridFamilyExecution, `DirectedFlowCutGap.GridFamilyGuard, `DirectedFlowCutGap.GridFamilyGuessCall, `DirectedFlowCutGap.GridFamilyHead, `DirectedFlowCutGap.GridFamilyOriginal, `DirectedFlowCutGap.GridFamilyPrimitiveCalls, `DirectedFlowCutGap.GridFamilyProgram, `DirectedFlowCutGap.GridFamilySpecification, `DirectedFlowCutGap.GridFamilyTrace]
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
    logInfo m!"GRID_FAMILY_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"GRID_FAMILY_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.GridFamily.program, `DirectedFlowCutGap.GridFamily.child_return, `DirectedFlowCutGap.GridFamily.context_extend, `DirectedFlowCutGap.GridFamily.result_extend, `DirectedFlowCutGap.GridFamily.list_extend, `DirectedFlowCutGap.GridFamily.zero_helper, `DirectedFlowCutGap.GridFamily.increment_helper, `DirectedFlowCutGap.GridFamily.predecessor_helper, `DirectedFlowCutGap.GridFamily.guess_helper, `DirectedFlowCutGap.GridFamily.guard_prefix, `DirectedFlowCutGap.GridFamily.empty_return, `DirectedFlowCutGap.GridFamily.head_run, `DirectedFlowCutGap.GridFamily.advance_run, `DirectedFlowCutGap.GridFamily.loop_return, `DirectedFlowCutGap.GridFamily.compute, `DirectedFlowCutGap.GridFamily.values_original, `DirectedFlowCutGap.GridFamily.values_length, `DirectedFlowCutGap.GridFamily.values_none, `DirectedFlowCutGap.GridFamily.family_bit] do
    IO.eprintln s!"GRID_FAMILY_CLOSURE_BEGIN {root}"
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
    logInfo m!"GRID_FAMILY_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
