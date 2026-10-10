import DirectedFlowCutGap.BinaryRetainedTape
import DirectedFlowCutGap.BinaryWeightedSamplingLaw

/-!
# Actual bounded fair-bit law at every retained-tape callback

The callback is the existing binary program, including its entering physical
ledger, bounded rejection, legal defaults and charged decoding. Its tape
marginal is independent of the ledger and is exactly the lowered draw-tree
law. Comparing that finite tape observable with the ideal law gives the
explicit per-callback error budget. The full output/ledger type is not finite.

This does not compose the error through an entire stateful graph query, or
identify bounded rejection with exact ideal uniformity. Counters and charges
are not erased from the executable callback; only the proof observable is
projected. No executable definition or new runtime estimate is introduced.
-/
namespace DirectedFlowCutGap.BinaryRetainedTapeLaw
noncomputable section
open BinaryArithmetic BinarySamplerMetadata RetainedGridState
open BinaryWeightedSamplingLaw
variable {n L : ℕ}

theorem sampleTape_law (fuel cutoff : Bits) (hcut : value cutoff=L) (hL : 0<L)
    (a : PairFlags n) (s : Ledger) :
    (BinaryRetainedTape.sampleTape fairBit fuel cutoff hcut hL a s).map Prod.fst =
      FiniteDrawTrees.ideal
        (LazyFairBitTrees.lower (value fuel) (RetainedDrawTrees.sampleTape hL a)) := by
  change Prod.fst <$> BinaryRetainedTape.sampleTape fairBit fuel cutoff hcut hL a s = _
  rw [BinaryRetainedTape.sampleTape_lower,fairBit_index]
  exact execute_binary_ideal (LazyFairBitTrees.lower_binary _ _)

/-- The incoming ledger and the locally reset operation subtotal do not
change the actual tape law. This is a conditional law at each reached state. -/
theorem callback_law (fuel cutoff : Bits) (hcut : value cutoff=L) (hL : 0<L)
    (a : PairFlags n) (s : Ledger) :
    ((BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a).run s).map
        (fun out => out.1.1) =
      FiniteDrawTrees.ideal
        (LazyFairBitTrees.lower (value fuel) (RetainedDrawTrees.sampleTape hL a)) := by
  change (fun out => out.1.1) <$>
    (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a).run s = _
  rw [BinaryRetainedTape.callback_projection,← MonadicBitSampler.execute_lower_refines,
    fairBit_index]
  exact execute_binary_ideal (LazyFairBitTrees.lower_binary _ _)

/-- A fresh finite-tape event bound at every ledger, with all bounded
rejection defaults included, rather than an assumed exact sampler law. -/
theorem callback_event_le [NeZero L]
    (fuel cutoff : Bits) (hcut : value cutoff=L) (hL : 0<L)
    (a : PairFlags n) (s : Ledger) (P : RetainedTapeInput.Tape L a → Prop) :
    FiniteAmplification.probability
      (((BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a).run s).map
        (fun out => out.1.1)) P ≤
      FiniteAmplification.probability (RetainedExecutionLaw.sampleTape a) P +
        ((2*n*n : ℕ) : ℝ)*((1 : ℝ)/2)^(value fuel) := by
  rw [callback_law]
  have h := LazyFairBitTrees.lowered_event_le
    (RetainedDrawTrees.sampleTape_within hL a) (value fuel) P
  rw [RetainedDrawTrees.sampleTape_law] at h
  exact h

end
end DirectedFlowCutGap.BinaryRetainedTapeLaw
