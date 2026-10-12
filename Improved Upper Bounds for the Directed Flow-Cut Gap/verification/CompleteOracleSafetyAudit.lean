import DirectedFlowCutGap.OracleChoiceProgram
import DirectedFlowCutGap.OracleChoiceCalls
import DirectedFlowCutGap.OracleDefaultMask
import DirectedFlowCutGap.OracleEmptyChoice
import DirectedFlowCutGap.OracleSelectedMask
import DirectedFlowCutGap.OracleChoiceData
import DirectedFlowCutGap.OracleCapacityCall
import DirectedFlowCutGap.OracleCapacityFinish
import DirectedFlowCutGap.OracleChoiceCapacity
import DirectedFlowCutGap.OracleChoiceExecution
import DirectedFlowCutGap.ActualOracleChoice
import DirectedFlowCutGap.GraphOracleProgram
import DirectedFlowCutGap.GraphOracleDemandCall
import DirectedFlowCutGap.GraphOracleChoiceCall
import DirectedFlowCutGap.GraphOracleExecution
import DirectedFlowCutGap.GraphOracleBounds
import DirectedFlowCutGap.ActualGraphOracle
import DirectedFlowCutGap.ActualCapacityBottleneck
import DirectedFlowCutGap.ActualDemandOrigin
import DirectedFlowCutGap.ActualOracleMask
import DirectedFlowCutGap.CapacityBottleneckBounds
import DirectedFlowCutGap.CapacityBottleneckEncoding
import DirectedFlowCutGap.CapacityBottleneckProgram
import DirectedFlowCutGap.CapacityBottleneckRefinement
import DirectedFlowCutGap.CapacityBottleneckSelection
import DirectedFlowCutGap.CapacityCandidateConstruction
import DirectedFlowCutGap.CapacityCandidateStep
import DirectedFlowCutGap.DemandSelectionOrigin
import DirectedFlowCutGap.OracleMaskBounds
import DirectedFlowCutGap.OracleMaskComparison
import DirectedFlowCutGap.OracleMaskConstruction
import DirectedFlowCutGap.OracleMaskProgram
import DirectedFlowCutGap.OracleMaskRefinement
import DirectedFlowCutGap.OracleMaskTail
import DirectedFlowCutGap.OracleMaskVertex
import DirectedFlowCutGap.OracleTailMembership
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "ORACLE_COMPONENT_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.OracleChoiceProgram,`DirectedFlowCutGap.OracleChoiceCalls,`DirectedFlowCutGap.OracleDefaultMask,`DirectedFlowCutGap.OracleEmptyChoice,`DirectedFlowCutGap.OracleSelectedMask,`DirectedFlowCutGap.OracleChoiceData,`DirectedFlowCutGap.OracleCapacityCall,`DirectedFlowCutGap.OracleCapacityFinish,`DirectedFlowCutGap.OracleChoiceCapacity,`DirectedFlowCutGap.OracleChoiceExecution,`DirectedFlowCutGap.ActualOracleChoice,`DirectedFlowCutGap.GraphOracleProgram,`DirectedFlowCutGap.GraphOracleDemandCall,`DirectedFlowCutGap.GraphOracleChoiceCall,`DirectedFlowCutGap.GraphOracleExecution,`DirectedFlowCutGap.GraphOracleBounds,`DirectedFlowCutGap.ActualGraphOracle,
    `DirectedFlowCutGap.ActualCapacityBottleneck,
    `DirectedFlowCutGap.ActualDemandOrigin,
    `DirectedFlowCutGap.ActualOracleMask,
    `DirectedFlowCutGap.CapacityBottleneckBounds,
    `DirectedFlowCutGap.CapacityBottleneckEncoding,
    `DirectedFlowCutGap.CapacityBottleneckProgram,
    `DirectedFlowCutGap.CapacityBottleneckRefinement,
    `DirectedFlowCutGap.CapacityBottleneckSelection,
    `DirectedFlowCutGap.CapacityCandidateConstruction,
    `DirectedFlowCutGap.CapacityCandidateStep,
    `DirectedFlowCutGap.DemandSelectionOrigin,
    `DirectedFlowCutGap.OracleMaskBounds,
    `DirectedFlowCutGap.OracleMaskComparison,
    `DirectedFlowCutGap.OracleMaskConstruction,
    `DirectedFlowCutGap.OracleMaskProgram,
    `DirectedFlowCutGap.OracleMaskRefinement,
    `DirectedFlowCutGap.OracleMaskTail,
    `DirectedFlowCutGap.OracleMaskVertex,
    `DirectedFlowCutGap.OracleTailMembership]
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
    logInfo m!"ORACLE_COMPONENT_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"ORACLE_COMPONENT_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.OracleMask.mask_return,
      `DirectedFlowCutGap.OracleMask.mask_encode,
      `DirectedFlowCutGap.OracleMask.mask_bit,
      `DirectedFlowCutGap.CapacityBottleneck.collect_return,
      `DirectedFlowCutGap.CapacityBottleneck.graph_high,
      `DirectedFlowCutGap.CapacityBottleneck.graph_bit,
      `DirectedFlowCutGap.DemandCollection.graph_origin_high,
      `DirectedFlowCutGap.OracleChoice.choice_return,
      `DirectedFlowCutGap.OracleChoice.choice_bit,
      `DirectedFlowCutGap.GraphOracleMachine.oracle_run,
      `DirectedFlowCutGap.GraphOracleMachine.oracle_bit] do
    IO.eprintln s!"ORACLE_COMPONENT_CLOSURE_BEGIN {root}"
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
    logInfo m!"ORACLE_COMPONENT_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
