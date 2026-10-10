import DirectedFlowCutGap.StatefulBoundedTapeLaw
import DirectedFlowCutGap.EncodedRoundingEntry

/-!
# Actual bounded fair-bit law of the charged encoded entry

The whole-monad charged/data projection preserves the same sampler ledger.
The returned cut, after the real entry's final conversion, is exactly the
bounded draw-tree observable. Its error is compared with the established
ideal core law. No exact-uniformity premise or finite full-record assumption
is introduced. All-regime guards, repeated selection and physical storage
realization remain separate.
-/
namespace DirectedFlowCutGap.EncodedBoundedTapeLaw
noncomputable section
open scoped NNReal
open RetainedGridState IntegerAdaptiveExecution EncodedIntegerShortestPaths
open BinaryArithmetic BinarySamplerMetadata BinaryWeightedSamplingLaw
open EncodedRoundingEntry EncodedRoundingInput EncodedRoundingBounds StatefulSamplerProjection

set_option backward.isDefEq.respectTransparency false
variable {n L : ℕ}

/-- The existing monadic projection preserves all physical ledger effects. -/
theorem charged_run_law (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
    (horder : F.base.enumeration.vertices=List.finRange n) (hL : 0<L)
    (fuel cutoff : Bits) (hcut : value cutoff=L)
    {demands : Finset (Pair n)} (R restartFuel epochs : ℕ)
    (source : Code (graph adjacency) demands L) (state : Ledger) :
    observe (EncodedSampledRounding.ChargedResult.logged <$>
      EncodedSampledRounding.runSampled adjacency F horder hL
        (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL)
        R restartFuel epochs source) state =
      FiniteDrawTrees.actual (value fuel)
        (RetainedDrawTrees.runTree
          (RetainedCandidateSolver.optimizer adjacency F horder hL) hL
          (cutOracle F.base.enumeration adjacency hL) R restartFuel epochs source) := by
  rw [EncodedSampledRounding.run_projectionM]
  exact StatefulBoundedTapeLaw.run_bounded_law fuel cutoff hcut _ hL _
    R restartFuel epochs source state

/-- The actual encoded factory and prepared demand mask fix the finite tree. -/
def coreTree (adjacency : PairFlags n) (hL : 0<L) :
    FiniteDrawTrees.Tree (Finset (Fin n)) :=
  let F := CandidateEnumeration.make n L
  let initial := prepare F.base.enumeration adjacency hL
  RetainedFairBitLaw.cutTree
    (RetainedCandidateSolver.optimizer adjacency F (CandidateEnumeration.fin_vertices n) hL)
    hL (cutOracle F.base.enumeration adjacency hL)
    (IntegerEpochParameters.restart n) (IntegerEpochParameters.fuel n+1)
    (IntegerEpochParameters.fuel n+1) initial.state

/-- Projecting the actual output vertices uses the entry's real output conversion. -/
theorem entry_cut_law (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (state : Ledger) :
    (observe (EncodedRoundingEntry.run
      (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL) state).map
      (fun out => out.vertices.toFinset) =
      FiniteDrawTrees.actual (value fuel) (coreTree adjacency hL) := by
  let F := CandidateEnumeration.make n L
  let initial := prepare F.base.enumeration adjacency hL
  have hlaw := charged_run_law adjacency F (CandidateEnumeration.fin_vertices n) hL
    fuel cutoff hcut (IntegerEpochParameters.restart n) (IntegerEpochParameters.fuel n+1)
    (IntegerEpochParameters.fuel n+1) initial.state state
  have hview := congrArg (fun law => law.map
    (fun d => cutSet d.result.cache.state.data.cut)) hlaw
  simpa only [EncodedRoundingEntry.run,observe_map,PMF.map_comp,Function.comp_def,
    output_set,EncodedEpochParameters.compute_restart,EncodedEpochParameters.compute_fuel,
    coreTree,RetainedFairBitLaw.cutTree,FiniteDrawTrees.actual,FiniteDrawTrees.law_map] using hview

/-- The ideal law is the already verified original core law, not a replacement
oracle contract supplied by the caller. -/
theorem coreTree_ideal [NeZero L] (adjacency : PairFlags n) (hL : 0<L) :
    FiniteDrawTrees.ideal (coreTree adjacency hL) =
      IntegerClosureAsymptotic.coreLaw (graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration := by
  let F := CandidateEnumeration.make n L
  let initial := prepare F.base.enumeration adjacency hL
  unfold coreTree
  rw [RetainedFairBitLaw.cutTree_law,RetainedCandidateSolver.optimizer_eq,cutOracle_eq]
  change RetainedExecutionLaw.outputLaw _ hL _ _ _ _ initial.state = _
  rw [show initial.state = RetainedGridState.initialMaskedCode (graph adjacency)
      (by exact_mod_cast (show 1 ≤ L by omega)) initial.mask initial.correct from
    prepare_state F.base.enumeration adjacency hL]
  simpa only [RetainedClosureLaw.maskedLaw,RetainedExecutionLaw.sampledRunLaw_output] using
    (RetainedClosureLaw.maskedLaw_eq_coreLaw hL F.base.enumeration F.network.enumeration
      initial.mask initial.correct)

/-- Every callback's bounded/default branch is charged in the tree error budget. -/
theorem entry_event_le [NeZero L] (fuel cutoff : Bits) (hcut : value cutoff=L)
    (adjacency : PairFlags n) (hL : 0<L) (state : Ledger)
    (P : Finset (Fin n) → Prop) :
    FiniteAmplification.probability
      ((observe (EncodedRoundingEntry.run
        (BinaryRetainedTape.callback fairBit fuel cutoff hcut hL) adjacency hL) state).map
        (fun out => out.vertices.toFinset)) P ≤
      FiniteAmplification.probability
        (IntegerClosureAsymptotic.coreLaw (graph adjacency) L hL
          (CandidateEnumeration.make n L).network.enumeration) P +
        (((IntegerEpochParameters.fuel n+1)*(2*n*n) : ℕ) : ℝ)*((1 : ℝ)/2)^(value fuel) := by
  rw [entry_cut_law]
  have hb := RetainedDrawTrees.runTree_within
    (RetainedCandidateSolver.optimizer adjacency (CandidateEnumeration.make n L)
      (CandidateEnumeration.fin_vertices n) hL) hL
    (cutOracle (CandidateEnumeration.make n L).base.enumeration adjacency hL)
    (IntegerEpochParameters.restart n) (IntegerEpochParameters.fuel n+1)
    (IntegerEpochParameters.fuel n+1)
    (prepare (CandidateEnumeration.make n L).base.enumeration adjacency hL).state
  have h := FiniteDrawTrees.event_le
    (FiniteDrawTrees.within_map hb (fun d => cutSet d.result.cache.state.data.cut))
    (value fuel) P
  change FiniteAmplification.probability (FiniteDrawTrees.actual (value fuel)
      (coreTree adjacency hL)) P ≤
    FiniteAmplification.probability (FiniteDrawTrees.ideal (coreTree adjacency hL)) P + _ at h
  rw [coreTree_ideal] at h
  exact h

end
end DirectedFlowCutGap.EncodedBoundedTapeLaw
