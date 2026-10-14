import DirectedFlowCutGap.FinalDispatchProgram
import DirectedFlowCutGap.FinalDispatchCallLift
import DirectedFlowCutGap.FinalDispatchCalls
import DirectedFlowCutGap.FinalDispatchPrefix
import DirectedFlowCutGap.FinalDispatchOutput
import DirectedFlowCutGap.FinalDispatchPositive
import DirectedFlowCutGap.FinalDispatchTail
import DirectedFlowCutGap.FinalDispatchTrace
import DirectedFlowCutGap.ActualFinalDispatch
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! NEW, UNRUN exhaustive audit source. Select every declaration of all nine
new modules by indexed imported ModuleData.constNames, verify current ownership,
and deduplicate names. Traverse the complete type/body dependency closure UNION
of every selected declaration, including private/generated declarations. This is
not merely a selected-root audit or a namespace-prefix approximation. Running
this source later is separate from strict compilation and official kernel replay. -/
set_option stderrAsMessages false
#eval IO.eprintln "FINAL_DISPATCH_ALL_DECLARATIONS_IMPORT_READY"

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[
    `DirectedFlowCutGap.FinalDispatchProgram,
    `DirectedFlowCutGap.FinalDispatchCallLift,
    `DirectedFlowCutGap.FinalDispatchCalls,
    `DirectedFlowCutGap.FinalDispatchPrefix,
    `DirectedFlowCutGap.FinalDispatchOutput,
    `DirectedFlowCutGap.FinalDispatchPositive,
    `DirectedFlowCutGap.FinalDispatchTail,
    `DirectedFlowCutGap.FinalDispatchTrace,
    `DirectedFlowCutGap.ActualFinalDispatch]
  let mut roots : Array Name := #[]
  let mut rootSet : NameSet := {}
  for module in wanted do
    let some idx := env.getModuleIdx? module | throwError "Missing new module index: {module}"
    let some data := env.header.moduleData[idx.toNat]? | throwError "Missing new module data: {module}"
    let mut moduleCount := 0
    for name in data.constNames do
      -- A module's stale/exported inventory does not establish current ownership.
      if env.getModuleIdxFor? name == some idx && !rootSet.contains name then
        let some ci := env.find? name | throwError "Missing new declaration: {module}: {name}"
        if ci.isUnsafe then throwError "Unsafe new declaration: {module}: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden new-declaration axiom: {name}: {ax}"
        rootSet := rootSet.insert name
        roots := roots.push name
        moduleCount := moduleCount+1
        IO.eprintln s!"FINAL_DISPATCH_NEW_DECLARATION {module}|{name}"
    if moduleCount == 0 then throwError "No current-owned declarations selected for {module}"
    IO.eprintln s!"FINAL_DISPATCH_MODULE_AUDIT passed: {module}; {moduleCount} declarations"
  if roots.isEmpty then throwError "The all-new-declarations audit selected no roots"
  unless roots.size == rootSet.toList.length do throwError "Declaration root inventory has duplicates"
  IO.eprintln s!"FINAL_DISPATCH_ALL_DECLARATION_ROOTS {roots.size}"
  -- One visited set computes exactly the union closure without redoing shared
  -- dependencies thousands of times. getUsedConstantsAsSet examines both type
  -- and value (including opaque values), plus inductive/constructor/recursor links.
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut traversedEdges := 0
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    unless seen.contains name do
      seen := seen.insert name
      let some ci := env.find? name | throwError "Missing type/body closure declaration: {name}"
      if ci.isUnsafe then throwError "Unsafe type/body closure declaration: {name}"
      match ci with
      | .axiomInfo _ =>
        axioms := axioms.insert name
        unless allowed.contains name do throwError "Forbidden type/body closure axiom: {name}"
      | _ => pure ()
      for dep in ci.getUsedConstantsAsSet.toList do
        traversedEdges := traversedEdges+1
        unless seen.contains dep do todo := todo.push dep
  for root in roots do
    unless seen.contains root do throwError "A selected declaration was omitted from closure: {root}"
  IO.eprintln s!"FINAL_DISPATCH_ALL_NEW_TYPE_BODY_CLOSURE_UNION passed: {roots.size} roots; {seen.toList.length} constants; {traversedEdges} edges; axioms {axioms.toList}"
