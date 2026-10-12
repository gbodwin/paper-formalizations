import DirectedFlowCutGap.BinaryPointerListRead
import DirectedFlowCutGap.GraphAdjacencyProgram
import DirectedFlowCutGap.GraphWalkExtension
import DirectedFlowCutGap.GraphRelaxationProgram
import DirectedFlowCutGap.GraphRelaxationCalls
import DirectedFlowCutGap.GraphRelaxationAdapters
import DirectedFlowCutGap.GraphRelaxationFinish
import DirectedFlowCutGap.GraphRelaxationScan
import DirectedFlowCutGap.GraphRelaxationBounds
import DirectedFlowCutGap.GraphRelaxationExecution
import DirectedFlowCutGap.GraphRelaxationRefinement
import DirectedFlowCutGap.CostedCandidateMaterialization
import DirectedFlowCutGap.CostedCandidateSelection
import DirectedFlowCutGap.CostedCandidateBounds
import DirectedFlowCutGap.MaterializedGraphSelection
import DirectedFlowCutGap.IndexedRationalRead
import DirectedFlowCutGap.OutgoingCostProgram
import DirectedFlowCutGap.PathCostMaterialization
import DirectedFlowCutGap.MaterializedPathSum
import DirectedFlowCutGap.MaterializedGraphPath
import DirectedFlowCutGap.BinaryTrimProgram
import DirectedFlowCutGap.CanonicalArithmeticProgram
import DirectedFlowCutGap.CanonicalRationalAddition
import DirectedFlowCutGap.CanonicalRationalSum
import DirectedFlowCutGap.CanonicalPathCost
import DirectedFlowCutGap.RetainedArgminProgram
import DirectedFlowCutGap.RetainedGraphArgmin
import DirectedFlowCutGap.BinaryComparisonProgram
import DirectedFlowCutGap.RationalComparisonProgram
import DirectedFlowCutGap.InputRationalComparisonProgram
import DirectedFlowCutGap.RowTableValidationProgram
import DirectedFlowCutGap.SourceRowAcceptanceProgram
import DirectedFlowCutGap.ValidatedFractionalRows
import DirectedFlowCutGap.BinaryZeroProgram
import DirectedFlowCutGap.SourceRowValidationProgram
import DirectedFlowCutGap.BudgetOrderedPrefixProgram
import DirectedFlowCutGap.PackingBudgetProgram
import DirectedFlowCutGap.SourceRowReadProgram
import DirectedFlowCutGap.InputMultiplicationProgram
import DirectedFlowCutGap.InputAdditionProgram
import DirectedFlowCutGap.BinaryAdditionProgram
import DirectedFlowCutGap.SelfDelimitedWordProgram
import DirectedFlowCutGap.PreparedBinaryLength
import DirectedFlowCutGap.PreparedBinaryIncrement
import DirectedFlowCutGap.PreparedOrderedCounterPrefix
import DirectedFlowCutGap.PreparedRowEmit
import DirectedFlowCutGap.PreparedIndexedPairRead
import DirectedFlowCutGap.BinaryIndexedPairRead
import DirectedFlowCutGap.PreparedCounterPrefix
import DirectedFlowCutGap.FractionalHeapRead
import DirectedFlowCutGap.CounterPrefixProgram
import DirectedFlowCutGap.BinaryCounterProgram
import DirectedFlowCutGap.ConstructedPrefixMaterialization
import DirectedFlowCutGap.ReferencePrefixMaterialization
import DirectedFlowCutGap.PackedBooleanRead
import DirectedFlowCutGap.EncodedPackingBitBudget
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => match moduleNames[idx.toNat]? with
        | some mod => (`DirectedFlowCutGap).isPrefixOf mod
        | none => false
      | none => false
    if owned then
      count := count + 1
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {name}"
  if count == 0 then throwError "Reference source audit selected no declarations"
  logInfo m!"PASS exhaustive reference closure axiom audit: {count} declarations"
