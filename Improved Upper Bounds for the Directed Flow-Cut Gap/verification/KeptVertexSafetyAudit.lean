import DirectedFlowCutGap.ActualKeptVertex
import DirectedFlowCutGap.KeptVertexComparison
import DirectedFlowCutGap.KeptVertexEndpoints
import DirectedFlowCutGap.KeptVertexExecution
import DirectedFlowCutGap.KeptVertexFinish
import DirectedFlowCutGap.KeptVertexProgram
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "KEPT_VERTEX_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualKeptVertex,`DirectedFlowCutGap.KeptVertexComparison,`DirectedFlowCutGap.KeptVertexEndpoints,`DirectedFlowCutGap.KeptVertexExecution,`DirectedFlowCutGap.KeptVertexFinish,`DirectedFlowCutGap.KeptVertexProgram]
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
    logInfo m!"KEPT_VERTEX_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"KEPT_VERTEX_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.KeptVertex.program,`DirectedFlowCutGap.KeptVertex.compare_return,`DirectedFlowCutGap.KeptVertex.finish_return,`DirectedFlowCutGap.KeptVertex.endpoint_return,`DirectedFlowCutGap.KeptVertex.keep_return,`DirectedFlowCutGap.KeptVertex.keep_steps_bound,`DirectedFlowCutGap.KeptVertex.keep,`DirectedFlowCutGap.KeptVertex.keep_bit,`DirectedFlowCutGap.KeptVertex.bit_encode] do
    IO.eprintln s!"KEPT_VERTEX_CLOSURE_BEGIN {root}"
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
    logInfo m!"KEPT_VERTEX_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
