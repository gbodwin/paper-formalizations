import DirectedFlowCutGap.ActualAvoidingShortest
import DirectedFlowCutGap.AvoidingShortestBounds
import DirectedFlowCutGap.AvoidingShortestCallLift
import DirectedFlowCutGap.AvoidingShortestCalls
import DirectedFlowCutGap.AvoidingShortestExecution
import DirectedFlowCutGap.AvoidingShortestOriginal
import DirectedFlowCutGap.AvoidingShortestProgram
import DirectedFlowCutGap.AvoidingShortestRefinement
import DirectedFlowCutGap.AvoidingShortestTrace
import DirectedFlowCutGap.BinaryWalkCostCongruence
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "AVOIDING_SHORTEST_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualAvoidingShortest,`DirectedFlowCutGap.AvoidingShortestBounds,`DirectedFlowCutGap.AvoidingShortestCallLift,`DirectedFlowCutGap.AvoidingShortestCalls,`DirectedFlowCutGap.AvoidingShortestExecution,`DirectedFlowCutGap.AvoidingShortestOriginal,`DirectedFlowCutGap.AvoidingShortestProgram,`DirectedFlowCutGap.AvoidingShortestRefinement,`DirectedFlowCutGap.AvoidingShortestTrace,`DirectedFlowCutGap.BinaryWalkCostCongruence]
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
    logInfo m!"AVOIDING_SHORTEST_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"AVOIDING_SHORTEST_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.AvoidingShortest.program,`DirectedFlowCutGap.AvoidingShortest.zero_return,`DirectedFlowCutGap.AvoidingShortest.graph_return,`DirectedFlowCutGap.AvoidingShortest.search_return,`DirectedFlowCutGap.AvoidingShortest.typed_return,`DirectedFlowCutGap.AvoidingShortest.result_original,`DirectedFlowCutGap.BinaryFractionalWalkOracle.shortest_cost_eq,`DirectedFlowCutGap.AvoidingShortest.result_constant,`DirectedFlowCutGap.AvoidingShortest.steps_bound,`DirectedFlowCutGap.AvoidingShortest.search,`DirectedFlowCutGap.AvoidingShortest.search_bit] do
    IO.eprintln s!"AVOIDING_SHORTEST_CLOSURE_BEGIN {root}"
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
    logInfo m!"AVOIDING_SHORTEST_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
