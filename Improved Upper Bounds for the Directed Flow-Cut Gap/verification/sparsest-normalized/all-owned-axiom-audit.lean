import DirectedFlowCutGap.FiniteHarmonicThreshold
import DirectedFlowCutGap.SparsestVertexBridge
import DirectedFlowCutGap.SparsestVertexCorollary
import DirectedFlowCutGap.SparsestEdgeBridge
import DirectedFlowCutGap.SparsestEdgeCorollary
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let targetModules : Array Name := #[`DirectedFlowCutGap.FiniteHarmonicThreshold, `DirectedFlowCutGap.SparsestVertexBridge, `DirectedFlowCutGap.SparsestVertexCorollary, `DirectedFlowCutGap.SparsestEdgeBridge, `DirectedFlowCutGap.SparsestEdgeCorollary]
  for targetModule in targetModules do
    let mut count : Nat := 0
    for (name, _) in env.constants.toList do
      let included := match env.getModuleIdxFor? name with
        | some idx => match moduleNames[idx.toNat]? with
          | some m => m == targetModule
          | none => false
        | none => false
      if included then
        count := count + 1
        logInfo m!"AUDIT {name}"
        for ax in (← Lean.collectAxioms name) do
          unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
    if count == 0 then throwError "No declarations audited in {targetModule}"
    logInfo m!"Axiom audit passed for all {count} declarations defined in {targetModule}."
