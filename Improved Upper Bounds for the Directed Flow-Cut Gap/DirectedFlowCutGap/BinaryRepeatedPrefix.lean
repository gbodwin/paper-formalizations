import DirectedFlowCutGap.BinaryRepetitionTrees

/-! A fixed independent bit prefix realizes the entire guarded repeated
rounding program, including all samples, its actual minimum selector and the
same cumulative physical ledger. Budget construction and physical storage
costs are not established by this finite-law equality. -/
namespace DirectedFlowCutGap.BinaryRepeatedPrefix
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees LazyFairBitTrees MonadicBitSampler RetainedGridState
variable {n L : ℕ} (fuel cutoff : Bits) (hcut : value cutoff=L)
  (adjacency : PairFlags n) (hL : 0<L)

abbrev tree (extra : ℕ) (state : Ledger) :=
  (EncodedRoundingRepetition.run (callback BinarySamplerTrees.bit fuel cutoff hcut hL)
    adjacency hL extra).run state

theorem execute {M : Type → Type} [Monad M] [LawfulMonad M] (b : M (Fin 2))
    (extra : ℕ) (state : Ledger) :
    FiniteDrawTrees.execute (liftBit b) (tree fuel cutoff hcut adjacency hL extra state) =
      (EncodedRoundingRepetition.run (callback (BinaryTapeTrees.boolBit b) fuel cutoff hcut hL)
        adjacency hL extra).run state :=
  BinaryRepetitionTrees.repeat_execute b _ _
    (fun s => BinaryEntryTrees.all_execute fuel cutoff hcut adjacency hL b s) extra state

theorem binary (extra : ℕ) (state : Ledger) :
    Binary (tree fuel cutoff hcut adjacency hL extra state) :=
  BinaryRepetitionTrees.repeat_binary _
    (fun s => BinaryEntryTrees.all_binary fuel cutoff hcut adjacency hL s) extra state

theorem within (extra : ℕ) (state : Ledger) :
    Within ((extra+1)*BinaryEntryTrees.budget n fuel cutoff)
      (tree fuel cutoff hcut adjacency hL extra state) :=
  BinaryRepetitionTrees.repeat_within _ _
    (fun s => BinaryEntryTrees.all_within fuel cutoff hcut adjacency hL s) extra state

theorem same_stream (extra : ℕ) (state : Ledger) :
    (EncodedRoundingRepetition.run (callback BinaryTrackedPrefix.next fuel cutoff hcut hL)
      adjacency hL extra).run state =
      FiniteBinaryPrefix.run (tree fuel cutoff hcut adjacency hL extra state) :=
  (execute fuel cutoff hcut adjacency hL FiniteBinaryPrefix.next extra state).symm

noncomputable section
private theorem fair_law (extra : ℕ) (state : Ledger) :
    ideal (tree fuel cutoff hcut adjacency hL extra state) =
      (EncodedRoundingRepetition.run (callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL)
        adjacency hL extra).run state := by
  rw [← BinaryWeightedSamplingLaw.execute_binary_ideal
    (binary fuel cutoff hcut adjacency hL extra state)]
  simpa only [BinaryTapeTrees.boolBit,BinaryWeightedSamplingLaw.fairBit,PMF.monad_map_eq_map] using
    execute fuel cutoff hcut adjacency hL (PMF.uniformOfFintype (Fin 2)) extra state

theorem output_law (extra : ℕ) (state : Ledger) :
    (FiniteBinaryPrefix.prefixLaw ((extra+1)*BinaryEntryTrees.budget n fuel cutoff)).map
      (fun xs => (((EncodedRoundingRepetition.run
        (callback BinaryTrackedPrefix.next fuel cutoff hcut hL) adjacency hL extra).run state).run xs).1) =
      (EncodedRoundingRepetition.run (callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL)
        adjacency hL extra).run state := by
  rw [same_stream,FiniteBinaryPrefix.output_law
    (within fuel cutoff hcut adjacency hL extra state) (binary fuel cutoff hcut adjacency hL extra state)]
  exact fair_law fuel cutoff hcut adjacency hL extra state

theorem actual_supported (extra : ℕ) (state : Ledger) (xs : List (Fin 2)) :
    (((EncodedRoundingRepetition.run (callback BinaryTrackedPrefix.next fuel cutoff hcut hL)
      adjacency hL extra).run state).run xs).1 ∈
      ((EncodedRoundingRepetition.run (callback BinaryWeightedSamplingLaw.fairBit fuel cutoff hcut hL)
        adjacency hL extra).run state).support := by
  rw [same_stream,← fair_law]
  exact BinaryFullPrefixCost.run_supported (binary fuel cutoff hcut adjacency hL extra state) xs

end
end DirectedFlowCutGap.BinaryRepeatedPrefix
