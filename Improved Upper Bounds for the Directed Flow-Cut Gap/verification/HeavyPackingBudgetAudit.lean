import DirectedFlowCutGap.StoredInputPackingPrefix
import DirectedFlowCutGap.ConstructedPackingPrefix
import DirectedFlowCutGap.BinaryControllerPrefix
import DirectedFlowCutGap.BinaryControllerTrees
import DirectedFlowCutGap.BinaryEntryTrees
import DirectedFlowCutGap.BinaryFullPrefix
import DirectedFlowCutGap.BinaryFullPrefixCost
import DirectedFlowCutGap.BinaryHeavyPrefix
import DirectedFlowCutGap.BinaryHeavyProviderTrees
import DirectedFlowCutGap.BinaryPackingBudget
import DirectedFlowCutGap.BinaryPackingPrefixBudget
import DirectedFlowCutGap.BinaryPackingTrees
import DirectedFlowCutGap.BinaryRepeatedPrefix
import DirectedFlowCutGap.BinaryRepetitionTrees
import DirectedFlowCutGap.BinarySamplerTrees
import DirectedFlowCutGap.BinaryTapeBudget
import DirectedFlowCutGap.BinaryTapePrefix
import DirectedFlowCutGap.BinaryTapeTrees
import DirectedFlowCutGap.BinaryTicketTrees
import DirectedFlowCutGap.BinaryTrackedPrefix
import DirectedFlowCutGap.BinaryWeightedPackingTrees
import DirectedFlowCutGap.BinaryWeightedTrees
import DirectedFlowCutGap.FiniteBinaryPrefix
import DirectedFlowCutGap.FiniteHeavyCertificate
import DirectedFlowCutGap.FiniteRoundingCertificate
import DirectedFlowCutGap.FiniteSupportTrees
import DirectedFlowCutGap.HeavyPackingEntry
import DirectedFlowCutGap.HeavyPackingPrefix
import DirectedFlowCutGap.HeavyQueryBitBudget
import DirectedFlowCutGap.QueryBudgetArithmetic
import DirectedFlowCutGap.QueryBudgetPolynomial
import DirectedFlowCutGap.StatefulHeavyPathwise
import DirectedFlowCutGap.StatefulTreeInterpreter
import DirectedFlowCutGap.HeavyPackingBitBudget
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
  if count == 0 then throwError "Probability source audit selected no declarations"
  logInfo m!"PASS exhaustive repetition probability closure axiom audit: {count} declarations"
