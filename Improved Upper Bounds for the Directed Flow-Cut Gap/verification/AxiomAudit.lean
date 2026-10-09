import DirectedFlowCutGap
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let root : Name := `DirectedFlowCutGap
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let included := match env.getModuleIdxFor? name with
      | some idx => match moduleNames[idx.toNat]? with
        | some m => root.isPrefixOf m
        | none => false
      | none => false
    if included then
      count := count + 1
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then throwError "No declarations audited"
  logInfo m!"Axiom audit passed for {count} declarations in the 153-module DirectedFlowCutGap checkpoint."
#print axioms DirectedFlowCutGap.exists_finite_mw_family
#print axioms DirectedFlowCutGap.cutsPair_iff_endpointDeletedGraph

#print axioms DirectedFlowCutGap.PackingCovering.strong_duality

#print axioms DirectedFlowCutGap.exists_finite_nonnegative_mw_family
#print axioms DirectedFlowCutGap.VertexFlow.strong_duality
#print axioms DirectedFlowCutGap.TerminalPorts.vertexDistance_eq
#print axioms DirectedFlowCutGap.WitnessThinning.source_scale_bounds

#print axioms DirectedFlowCutGap.EpochAccounting.restart_log_bound
#print axioms DirectedFlowCutGap.FiniteSurvival.subset_product_average_le_exp

#print axioms DirectedFlowCutGap.FiniteCutLaw.expected_new_cost_le
