import DirectedFlowCutGap.SupportRecoveryProgram
import DirectedFlowCutGap.SupportSearchData
import DirectedFlowCutGap.SupportSearchAccounts
import DirectedFlowCutGap.SupportRecoveryCalls
import DirectedFlowCutGap.SupportSearchInvariants
import DirectedFlowCutGap.SupportEdgeComparison
import DirectedFlowCutGap.SupportEdgeMembership
import DirectedFlowCutGap.SupportAdjacencyTest
import DirectedFlowCutGap.SupportCodeLookup
import DirectedFlowCutGap.SupportPredecessorPrefix
import DirectedFlowCutGap.SupportPredecessorScan
import DirectedFlowCutGap.SupportVisitAllocation
import DirectedFlowCutGap.SupportVisitDecision
import DirectedFlowCutGap.SupportVertexVisit
import DirectedFlowCutGap.SupportForwardTransitions
import DirectedFlowCutGap.SupportForwardPass
import DirectedFlowCutGap.SupportRoundInitial
import DirectedFlowCutGap.SupportRounds
import DirectedFlowCutGap.SupportSearchExecution
import DirectedFlowCutGap.SupportSearchLowerMachine
import DirectedFlowCutGap.SupportRetainedData
import DirectedFlowCutGap.SupportSearchEncoding
import DirectedFlowCutGap.SupportRetainedScans
import DirectedFlowCutGap.SupportRetainedVisit
import DirectedFlowCutGap.SupportRetainedSearch
import DirectedFlowCutGap.SupportPrimitiveBounds
import DirectedFlowCutGap.SupportIterationBounds
import DirectedFlowCutGap.ActualSupportSearch
import DirectedFlowCutGap.RecoveredEdgeProjection
import DirectedFlowCutGap.CostedSupportProgram
import DirectedFlowCutGap.CostedSupportCalls
import DirectedFlowCutGap.CostedSupportContinuation
import DirectedFlowCutGap.CostedSupportExecution
import DirectedFlowCutGap.CostedSupportRefinement
import DirectedFlowCutGap.ActualCostedRecovery
import DirectedFlowCutGap.GraphRecoveryController
import DirectedFlowCutGap.GraphRecoveryContext
import DirectedFlowCutGap.GraphRecoveryCalls
import DirectedFlowCutGap.GraphRecoveryFinish
import DirectedFlowCutGap.GraphRecoveryRefinement
import DirectedFlowCutGap.GraphRecoveryExecution
import DirectedFlowCutGap.GraphRecoverySize
import DirectedFlowCutGap.GraphRecoveryBounds
import DirectedFlowCutGap.ActualGraphShortest
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option stderrAsMessages false
#eval IO.eprintln "GRAPH_SHORTEST_AUDIT_IMPORTED"
open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let wanted : Array Name := #[`DirectedFlowCutGap.SupportRecoveryProgram,
    `DirectedFlowCutGap.SupportSearchData,
    `DirectedFlowCutGap.SupportSearchAccounts,
    `DirectedFlowCutGap.SupportRecoveryCalls,
    `DirectedFlowCutGap.SupportSearchInvariants,
    `DirectedFlowCutGap.SupportEdgeComparison,
    `DirectedFlowCutGap.SupportEdgeMembership,
    `DirectedFlowCutGap.SupportAdjacencyTest,
    `DirectedFlowCutGap.SupportCodeLookup,
    `DirectedFlowCutGap.SupportPredecessorPrefix,
    `DirectedFlowCutGap.SupportPredecessorScan,
    `DirectedFlowCutGap.SupportVisitAllocation,
    `DirectedFlowCutGap.SupportVisitDecision,
    `DirectedFlowCutGap.SupportVertexVisit,
    `DirectedFlowCutGap.SupportForwardTransitions,
    `DirectedFlowCutGap.SupportForwardPass,
    `DirectedFlowCutGap.SupportRoundInitial,
    `DirectedFlowCutGap.SupportRounds,
    `DirectedFlowCutGap.SupportSearchExecution,
    `DirectedFlowCutGap.SupportSearchLowerMachine,
    `DirectedFlowCutGap.SupportRetainedData,
    `DirectedFlowCutGap.SupportSearchEncoding,
    `DirectedFlowCutGap.SupportRetainedScans,
    `DirectedFlowCutGap.SupportRetainedVisit,
    `DirectedFlowCutGap.SupportRetainedSearch,
    `DirectedFlowCutGap.SupportPrimitiveBounds,
    `DirectedFlowCutGap.SupportIterationBounds,
    `DirectedFlowCutGap.ActualSupportSearch,
    `DirectedFlowCutGap.RecoveredEdgeProjection,
    `DirectedFlowCutGap.CostedSupportProgram,
    `DirectedFlowCutGap.CostedSupportCalls,
    `DirectedFlowCutGap.CostedSupportContinuation,
    `DirectedFlowCutGap.CostedSupportExecution,
    `DirectedFlowCutGap.CostedSupportRefinement,
    `DirectedFlowCutGap.ActualCostedRecovery,
    `DirectedFlowCutGap.GraphRecoveryController,
    `DirectedFlowCutGap.GraphRecoveryContext,
    `DirectedFlowCutGap.GraphRecoveryCalls,
    `DirectedFlowCutGap.GraphRecoveryFinish,
    `DirectedFlowCutGap.GraphRecoveryRefinement,
    `DirectedFlowCutGap.GraphRecoveryExecution,
    `DirectedFlowCutGap.GraphRecoverySize,
    `DirectedFlowCutGap.GraphRecoveryBounds,
    `DirectedFlowCutGap.ActualGraphShortest]
  let wantedSet : NameSet := wanted.foldl (fun seen name => seen.insert name) {}
  let mut counts : NameMap Nat := {}
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := modules[idx.toNat]!
      if wantedSet.contains module then
        counts := counts.insert module ((counts.find? module).getD 0+1)
        count := count+1
        if ci.isUnsafe then throwError "Unsafe graph shortest declaration: {name}"
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do throwError "Forbidden graph shortest axiom: {name}: {ax}"
  for module in wanted do
    let found := (counts.find? module).getD 0
    if found == 0 then throwError "No declarations audited for {module}"
    logInfo m!"GRAPH_SHORTEST_MODULE_AUDIT passed: {module}; {found} declarations"
  logInfo m!"GRAPH_SHORTEST_DECLARATION_AUDIT passed: {count} declarations"
  for root in #[`DirectedFlowCutGap.SupportRecoveryProgram.member_return,
      `DirectedFlowCutGap.SupportRecoveryProgram.predecessor_return,
      `DirectedFlowCutGap.SupportRecoveryProgram.pass_return,
      `DirectedFlowCutGap.SupportRecoveryProgram.rounds_return,
      `DirectedFlowCutGap.SupportRecoveryProgram.search_bit,
      `DirectedFlowCutGap.SupportSearchEncoding.graph_bit,
      `DirectedFlowCutGap.CostedSupportProgram.graph_bit,
      `DirectedFlowCutGap.GraphRecoveryController.graph_bit] do
    IO.eprintln s!"GRAPH_SHORTEST_CLOSURE_BEGIN {root}"
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
    logInfo m!"GRAPH_SHORTEST_TYPE_BODY_CLOSURE passed: {root}; {seen.toList.length} constants; axioms {axioms.toList}"
