import DirectedFlowCutGap.StatefulSamplerProjection
import DirectedFlowCutGap.BinaryRetainedTapeLaw
import DirectedFlowCutGap.RetainedFairBitLaw

/-!
# Bounded fair-bit law through the stateful retained data controller

The physical sampler ledger is retained across every adaptive callback. Its
tape marginal at each entering ledger is the already proved bounded law, so
the complete graph-level result law is the actual finite draw-tree law. The
event error is applied only to the finite cut observable, never to the full
result records or ledger.

This composes the actual binary callback through the retained data controller.
The charged encoded entry, all-regime guards and repeated selector still need
their named observable joins. No new runtime/storage substitution is claimed.
-/
namespace DirectedFlowCutGap.StatefulBoundedTapeLaw
noncomputable section
open scoped NNReal
open RetainedGridState IntegerAdaptiveExecution RetainedDrawTrees
open BinaryArithmetic BinarySamplerMetadata BinaryWeightedSamplingLaw
open StatefulSamplerProjection

variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
variable {selector : FlexibleCandidateSchedule.FamilyProvider G D (L : ℝ≥0) → Prop}
variable {H : ∃ P, selector P}

/-- The tree law commutes with the existing controller for any primitive law,
not only uniform draws. This does not require a finite output type. -/
theorem executeTree_law (primitive : (k : ℕ) → (0 < k) → PMF (Fin k))
    (Q : Optimizer H) (hL : 0<L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (c : Cache H) :
    FiniteDrawTrees.law primitive (executeTree Q hL C R restartFuel epochs c) =
      RetainedSampledExecution.executeSampled
        (fun a => FiniteDrawTrees.law primitive (sampleTape hL a))
        Q hL C R restartFuel epochs c := by
  induction epochs generalizing c with
  | zero => rfl
  | succ epochs ih =>
      simp only [executeTree,RetainedSampledExecution.executeSampled]
      split_ifs with hz
      · rfl
      · change FiniteDrawTrees.law primitive (FiniteDrawTrees.bind (sampleTape hL _) _) = _
        rw [FiniteDrawTrees.law_bind]
        congr 1
        funext t
        change FiniteDrawTrees.law primitive (FiniteDrawTrees.bind _ _) = _
        rw [FiniteDrawTrees.law_bind]
        simp only [executeTree] at ih
        rw [ih]
        rfl

theorem runTree_law (primitive : (k : ℕ) → (0 < k) → PMF (Fin k))
    (Q : Optimizer H) (hL : 0<L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (source : Code G D L) :
    FiniteDrawTrees.law primitive (runTree Q hL C R restartFuel epochs source) =
      RetainedSampledExecution.runSampled
        (fun a => FiniteDrawTrees.law primitive (sampleTape hL a))
        Q hL C R restartFuel epochs source := by
  unfold runTree RetainedSampledExecution.runSampled
  change FiniteDrawTrees.law primitive (FiniteDrawTrees.bind _ _) = _
  rw [FiniteDrawTrees.law_bind]
  rw [show FiniteDrawTrees.law primitive
      (RetainedSampledExecution.executeSampled (sampleTape hL)
        Q hL C R restartFuel epochs _) = _ from
    executeTree_law primitive Q hL C R restartFuel epochs _]
  rfl

theorem callback_observe (fuel cutoff : Bits) (hcut : value cutoff=L) (hL : 0<L)
    (a : PairFlags n) (state : Ledger) :
    observe (Prod.fst <$> BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a) state =
      FiniteDrawTrees.actual (value fuel) (sampleTape hL a) := by
  rw [observe_map]
  change (((BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a).run state).map
    Prod.fst).map Prod.fst = _
  rw [PMF.map_comp]
  change ((BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a).run state).map
    (fun out => out.1.1) = _
  rw [BinaryRetainedTapeLaw.callback_law,LazyFairBitTrees.lower_law]

/-- No independence of result and ledger is assumed. The callback law holds
at every entering ledger, including those selected by prior graph outcomes. -/
theorem run_bounded_law (fuel cutoff : Bits) (hcut : value cutoff=L)
    (Q : Optimizer H) (hL : 0<L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (source : Code G D L) (state : Ledger) :
    observe (RetainedSampledExecution.runSampled
        (fun a => Prod.fst <$> BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a)
        Q hL C R restartFuel epochs source) state =
      FiniteDrawTrees.actual (value fuel) (runTree Q hL C R restartFuel epochs source) := by
  rw [StatefulSamplerProjection.run_observe _
    (fun a => FiniteDrawTrees.actual (value fuel) (sampleTape hL a))
    (fun a state => callback_observe fuel cutoff hcut hL a state)]
  exact (runTree_law (FiniteDrawTrees.boundedDraw (value fuel))
    Q hL C R restartFuel epochs source).symm

theorem cut_bounded_law (fuel cutoff : Bits) (hcut : value cutoff=L)
    (Q : Optimizer H) (hL : 0<L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (source : Code G D L) (state : Ledger) :
    (observe (RetainedSampledExecution.runSampled
        (fun a => Prod.fst <$> BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a)
        Q hL C R restartFuel epochs source) state).map
        (fun d => cutSet d.result.cache.state.data.cut) =
      FiniteDrawTrees.actual (value fuel)
        (RetainedFairBitLaw.cutTree Q hL C R restartFuel epochs source) := by
  rw [run_bounded_law,RetainedFairBitLaw.cutTree]
  exact (FiniteDrawTrees.law_map (FiniteDrawTrees.boundedDraw (value fuel)) _ _).symm

/-- The concrete adaptive callback error is paid over the controller's actual
draw-tree budget, including all restart and bounded-default branches. -/
theorem cut_event_le [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
    (Q : Optimizer H) (hL : 0<L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (source : Code G D L) (state : Ledger)
    (P : Finset (Fin n) → Prop) :
    FiniteAmplification.probability
      ((observe (RetainedSampledExecution.runSampled
        (fun a => Prod.fst <$> BinaryRetainedTape.callback fairBit fuel cutoff hcut hL a)
        Q hL C R restartFuel epochs source) state).map
        (fun d => cutSet d.result.cache.state.data.cut)) P ≤
      FiniteAmplification.probability
        (RetainedExecutionLaw.outputLaw Q hL C R restartFuel epochs source) P +
          ((epochs*(2*n*n) : ℕ) : ℝ)*((1 : ℝ)/2)^(value fuel) := by
  rw [cut_bounded_law]
  have h := FiniteDrawTrees.event_le
    (FiniteDrawTrees.within_map (runTree_within Q hL C R restartFuel epochs source)
      (fun d => cutSet d.result.cache.state.data.cut)) (value fuel) P
  change FiniteAmplification.probability (FiniteDrawTrees.actual (value fuel)
      (RetainedFairBitLaw.cutTree Q hL C R restartFuel epochs source)) P ≤
    FiniteAmplification.probability (FiniteDrawTrees.ideal
      (RetainedFairBitLaw.cutTree Q hL C R restartFuel epochs source)) P + _ at h
  rw [RetainedFairBitLaw.cutTree_law] at h
  exact h

end
end DirectedFlowCutGap.StatefulBoundedTapeLaw
