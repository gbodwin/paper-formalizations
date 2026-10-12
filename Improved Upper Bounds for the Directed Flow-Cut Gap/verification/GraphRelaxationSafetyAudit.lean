import DirectedFlowCutGap.GraphRelaxationRefinement
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.BinaryPointerListRead,
    `DirectedFlowCutGap.GraphAdjacencyProgram,
    `DirectedFlowCutGap.GraphWalkExtension,
    `DirectedFlowCutGap.GraphRelaxationProgram,
    `DirectedFlowCutGap.GraphRelaxationCalls,
    `DirectedFlowCutGap.GraphRelaxationAdapters,
    `DirectedFlowCutGap.GraphRelaxationFinish,
    `DirectedFlowCutGap.GraphRelaxationScan,
    `DirectedFlowCutGap.GraphRelaxationBounds,
    `DirectedFlowCutGap.GraphRelaxationExecution,
    `DirectedFlowCutGap.GraphRelaxationRefinement]
  let mut count : Nat := 0
  for module in wanted do
    let mut found : Nat := 0
    for (name, ci) in env.constants.toList do
      let owned := match env.getModuleIdxFor? name with
        | some idx => modules[idx.toNat]! == module
        | none => false
      if owned then
        found := found + 1
        if ci.isUnsafe then throwError "Unsafe graph relaxation declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden graph relaxation axiom: {name}: {ax}"
    if found == 0 then throwError "No declarations audited for {module}"
    count := count + found
    logInfo m!"GRAPH_RELAXATION_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"GRAPH_RELAXATION_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.BinaryPointerListRead.read_return,
      `DirectedFlowCutGap.GraphAdjacencyProgram.read_return,
      `DirectedFlowCutGap.GraphWalkExtension.extend_high,
      `DirectedFlowCutGap.GraphRelaxationProgram.scan_return,
      `DirectedFlowCutGap.GraphRelaxationProgram.scan_bit,
      `DirectedFlowCutGap.GraphRelaxationRefinement.graph_bit] do
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
    logInfo m!"GRAPH_RELAXATION_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
