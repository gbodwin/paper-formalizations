import DirectedFlowCutGap.BinaryTapeBudget
import DirectedFlowCutGap.BinaryRetainedTapeCost

/-! A finite independent prefix executes the entire retained binary tape
callback, including both loops and its exact returned ledger. The source suffix
is retained pathwise; the distribution theorem observes the full callback
result and ledger. The branchwise bit budget and declared charge are separate
from physical memory, input/fuel construction, and whole-query execution. -/
namespace DirectedFlowCutGap.BinaryTapePrefix
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler

abbrev tree (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :=
  (callback BinarySamplerTrees.bit fuel cutoff hcut hL a).run s

theorem same_stream (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    (callback BinaryTrackedPrefix.next fuel cutoff hcut hL a).run s =
      FiniteBinaryPrefix.run (tree fuel cutoff hcut hL a s) :=
  (BinaryTapeTrees.callback_execute FiniteBinaryPrefix.next fuel cutoff hcut hL a s).symm

noncomputable section
private theorem fair_law (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    ideal (tree fuel cutoff hcut hL a s) =
      (callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL a).run s := by
  rw [← BinaryWeightedSamplingLaw.execute_binary_ideal
    (BinaryTapeBudget.callback_binary fuel cutoff hcut hL a s)]
  simpa only [BinaryTapeTrees.boolBit,BinaryWeightedSamplingLaw.fairBit,PMF.monad_map_eq_map]
    using BinaryTapeTrees.callback_execute (PMF.uniformOfFintype (Fin 2)) fuel cutoff hcut hL a s

/-- The same returned tape, incremental operation count and full ledger have
exactly the bounded fair-bit callback law. Only the reader suffix is projected. -/
theorem output_law (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    (FiniteBinaryPrefix.prefixLaw
      (BinaryTapeBudget.budget (RetainedTapeInput.activeList a).length fuel cutoff)).map
        (fun xs => (((callback BinaryTrackedPrefix.next fuel cutoff hcut hL a).run s).run xs).1) =
      (callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL a).run s := by
  rw [same_stream,FiniteBinaryPrefix.output_law
    (BinaryTapeBudget.callback_within fuel cutoff hcut hL a s)
    (BinaryTapeBudget.callback_binary fuel cutoff hcut hL a s)]
  exact fair_law fuel cutoff hcut hL a s

/-- This support statement also covers an exhausted list, whose actual reader
uses the supported zero fallback. No fresh execution is substituted. -/
theorem actual_supported (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) (xs : List (Fin 2)) :
    (((callback BinaryTrackedPrefix.next fuel cutoff hcut hL a).run s).run xs).1 ∈
      ((callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL a).run s).support := by
  rw [same_stream,← fair_law]
  exact BinaryFullPrefixCost.run_supported
    (BinaryTapeBudget.callback_binary fuel cutoff hcut hL a s) xs

theorem actual_charge (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) (xs : List (Fin 2)) :
    ((((callback BinaryTrackedPrefix.next fuel cutoff hcut hL a).run s).run xs).1).1.2 ≤
      BinaryRetainedTapeCost.callbackBound n fuel cutoff (ledgerWidth s) :=
  BinaryRetainedTapeCost.callback_charge BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL a s
    (actual_supported fuel cutoff hcut hL a s xs)

/-- The advertised increment is added exactly once to the entering operation
ledger of this same finite-stream execution. -/
theorem actual_operations (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) (xs : List (Fin 2)) :
    ((((callback BinaryTrackedPrefix.next fuel cutoff hcut hL a).run s).run xs).1).2.operations =
      s.operations+((((callback BinaryTrackedPrefix.next fuel cutoff hcut hL a).run s).run xs).1).1.2 :=
  (BinaryRetainedTapeCost.callback_bounds BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL a s
    (ledgerWidth s) le_rfl (actual_supported fuel cutoff hcut hL a s xs)).2.2.1

end
end DirectedFlowCutGap.BinaryTapePrefix
