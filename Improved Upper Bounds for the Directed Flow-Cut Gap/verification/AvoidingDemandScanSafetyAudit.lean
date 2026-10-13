import DirectedFlowCutGap.ActualAvoidingDemandScan
import DirectedFlowCutGap.AvoidingDemandScanCallLift
import DirectedFlowCutGap.AvoidingDemandScanCall
import DirectedFlowCutGap.AvoidingDemandScanHead
import DirectedFlowCutGap.AvoidingDemandScanExecution
import DirectedFlowCutGap.AvoidingDemandScanProgram
import DirectedFlowCutGap.AvoidingDemandScanTrace
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "AVOIDING_DEMAND_SCAN_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.ActualAvoidingDemandScan,`DirectedFlowCutGap.AvoidingDemandScanCallLift,`DirectedFlowCutGap.AvoidingDemandScanCall,`DirectedFlowCutGap.AvoidingDemandScanHead,`DirectedFlowCutGap.AvoidingDemandScanExecution,`DirectedFlowCutGap.AvoidingDemandScanProgram,`DirectedFlowCutGap.AvoidingDemandScanTrace]
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
    logInfo m!"AVOIDING_DEMAND_SCAN_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"AVOIDING_DEMAND_SCAN_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.AvoidingDemandScan.program,`DirectedFlowCutGap.AvoidingDemandScan.query_return,`DirectedFlowCutGap.AvoidingDemandScan.head_query,`DirectedFlowCutGap.AvoidingDemandScan.scan_return,`DirectedFlowCutGap.AvoidingDemandScan.result_original,`DirectedFlowCutGap.AvoidingDemandScan.scan,`DirectedFlowCutGap.AvoidingDemandScan.steps_bound,`DirectedFlowCutGap.AvoidingDemandScan.scan_bit] do
    IO.eprintln s!"AVOIDING_DEMAND_SCAN_CLOSURE_BEGIN {root}"
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
    logInfo m!"AVOIDING_DEMAND_SCAN_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
