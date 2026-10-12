import DirectedFlowCutGap.ActualGraphDiscovery
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "GRAPH_DISCOVERY_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.GraphDiscoveryProgram,
    `DirectedFlowCutGap.GraphDiscoveryCalls,
    `DirectedFlowCutGap.GraphVertexDecision,
    `DirectedFlowCutGap.GraphPassConstruction,
    `DirectedFlowCutGap.GraphRoundData,
    `DirectedFlowCutGap.GraphRoundCalls,
    `DirectedFlowCutGap.GraphBoundedRounds,
    `DirectedFlowCutGap.GraphLookupCalls,
    `DirectedFlowCutGap.GraphLookupDecision,
    `DirectedFlowCutGap.GraphLookupScan,
    `DirectedFlowCutGap.GraphMinimizeConstruction,
    `DirectedFlowCutGap.GraphDiscoveryRefinement,
    `DirectedFlowCutGap.GraphDiscoveryWidths,
    `DirectedFlowCutGap.GraphDiscoveryBounds,
    `DirectedFlowCutGap.GraphRoundBounds,
    `DirectedFlowCutGap.GraphDiscoveryExecution,
    `DirectedFlowCutGap.ActualGraphDiscovery]
  let wantedSet : NameSet := wanted.foldl (fun seen name => seen.insert name) {}
  let mut counts : NameMap Nat := {}
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := modules[idx.toNat]!
      if wantedSet.contains module then
        counts := counts.insert module ((counts.find? module).getD 0+1)
        count := count+1
        if ci.isUnsafe then throwError "Unsafe graph discovery declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden graph discovery axiom: {name}: {ax}"
  for module in wanted do
    let found := (counts.find? module).getD 0
    if found == 0 then throwError "No declarations audited for {module}"
    logInfo m!"GRAPH_DISCOVERY_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"GRAPH_DISCOVERY_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.GraphDiscoveryProgram.vertex_return,
      `DirectedFlowCutGap.GraphDiscoveryProgram.pass_return,
      `DirectedFlowCutGap.GraphDiscoveryProgram.rounds_return,
      `DirectedFlowCutGap.GraphDiscoveryProgram.lookup_return,
      `DirectedFlowCutGap.GraphDiscoveryProgram.minimize_return,
      `DirectedFlowCutGap.GraphDiscoveryProgram.minimize_bit,
      `DirectedFlowCutGap.ActualGraphDiscovery.graph_bit] do
    IO.eprintln s!"GRAPH_DISCOVERY_CLOSURE_BEGIN {root}"
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
    logInfo m!"GRAPH_DISCOVERY_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
