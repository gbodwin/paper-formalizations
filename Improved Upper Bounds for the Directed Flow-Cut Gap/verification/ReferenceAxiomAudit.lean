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
