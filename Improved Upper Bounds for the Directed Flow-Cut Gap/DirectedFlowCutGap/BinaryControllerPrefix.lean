import DirectedFlowCutGap.BinaryControllerTrees

/-! A finite independent bit prefix realizes the complete actual adaptive
controller output and ledger, while pathwise interpretation retains the reader
suffix. Random-dependent caches and all declared operation fields are included.
The epoch bound is explicit; physical storage/runtime and outer weighted/packing
execution remain separate. -/
namespace DirectedFlowCutGap.BinaryControllerPrefix
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler
open RetainedGridState IntegerAdaptiveExecution EncodedIntegerShortestPaths EncodedRoundingState
variable {n L : ℕ} (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
variable (horder : F.base.enumeration.vertices=List.finRange n) (hL : 0<L)
variable {demands : Finset (Pair n)}

abbrev tree (fuel cutoff : Bits) (hcut : value cutoff=L) (R restartFuel epochs : ℕ)
    (st : Code (graph adjacency) demands L) (state : Ledger) :=
  (EncodedSampledRounding.runSampled adjacency F horder hL
    (callback BinarySamplerTrees.bit fuel cutoff hcut hL) R restartFuel epochs st).run state

theorem same_stream (fuel cutoff : Bits) (hcut : value cutoff=L) (R restartFuel epochs : ℕ)
    (st : Code (graph adjacency) demands L) (state : Ledger) :
    (EncodedSampledRounding.runSampled adjacency F horder hL
      (callback BinaryTrackedPrefix.next fuel cutoff hcut hL) R restartFuel epochs st).run state =
      FiniteBinaryPrefix.run (tree adjacency F horder hL fuel cutoff hcut R restartFuel epochs st state) :=
  (BinaryControllerTrees.run_execute adjacency F horder hL FiniteBinaryPrefix.next
    fuel cutoff hcut R restartFuel epochs st state).symm

noncomputable section
private theorem fair_law (fuel cutoff : Bits) (hcut : value cutoff=L) (R restartFuel epochs : ℕ)
    (st : Code (graph adjacency) demands L) (state : Ledger) :
    ideal (tree adjacency F horder hL fuel cutoff hcut R restartFuel epochs st state) =
      (EncodedSampledRounding.runSampled adjacency F horder hL
        (callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL) R restartFuel epochs st).run state := by
  rw [← BinaryWeightedSamplingLaw.execute_binary_ideal
    (BinaryControllerTrees.run_binary adjacency F horder hL fuel cutoff hcut R restartFuel epochs st state)]
  simpa only [BinaryTapeTrees.boolBit,BinaryWeightedSamplingLaw.fairBit,PMF.monad_map_eq_map] using
    BinaryControllerTrees.run_execute adjacency F horder hL (PMF.uniformOfFintype (Fin 2))
      fuel cutoff hcut R restartFuel epochs st state

theorem output_law (fuel cutoff : Bits) (hcut : value cutoff=L) (R restartFuel epochs : ℕ)
    (st : Code (graph adjacency) demands L) (state : Ledger) :
    (FiniteBinaryPrefix.prefixLaw (epochs*BinaryControllerTrees.callBudget n fuel cutoff)).map
      (fun xs => (((EncodedSampledRounding.runSampled adjacency F horder hL
        (callback BinaryTrackedPrefix.next fuel cutoff hcut hL) R restartFuel epochs st).run state).run xs).1) =
      (EncodedSampledRounding.runSampled adjacency F horder hL
        (callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL) R restartFuel epochs st).run state := by
  rw [same_stream,FiniteBinaryPrefix.output_law
    (BinaryControllerTrees.run_within adjacency F horder hL fuel cutoff hcut R restartFuel epochs st state)
    (BinaryControllerTrees.run_binary adjacency F horder hL fuel cutoff hcut R restartFuel epochs st state)]
  exact fair_law adjacency F horder hL fuel cutoff hcut R restartFuel epochs st state

theorem actual_supported (fuel cutoff : Bits) (hcut : value cutoff=L) (R restartFuel epochs : ℕ)
    (st : Code (graph adjacency) demands L) (state : Ledger) (xs : List (Fin 2)) :
    (((EncodedSampledRounding.runSampled adjacency F horder hL
      (callback BinaryTrackedPrefix.next fuel cutoff hcut hL) R restartFuel epochs st).run state).run xs).1 ∈
      ((EncodedSampledRounding.runSampled adjacency F horder hL
        (callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL) R restartFuel epochs st).run state).support := by
  rw [same_stream,← fair_law]
  exact BinaryFullPrefixCost.run_supported
    (BinaryControllerTrees.run_binary adjacency F horder hL fuel cutoff hcut R restartFuel epochs st state) xs

end
end DirectedFlowCutGap.BinaryControllerPrefix
