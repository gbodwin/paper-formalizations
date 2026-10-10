import DirectedFlowCutGap.BinaryApproximatePackingMarginal
import DirectedFlowCutGap.BinaryApproximatePackingProbability
import DirectedFlowCutGap.BinaryZeroAvoidingProbability

/-!
# The actual zero-safe weighted packing and sampling composition

This wrapper executes the positive auxiliary-capacity preparation, the cached
monadic packing controller with the actual zero-avoiding provider, and one
finite-bit weighted draw. It retains the complete controller history and
sampler record, and adds their operation charges. Proof-side real parameters
never enter the executable body. Original graph validity, support validity and
the original all-cost provider's same-query quality remain named premises.

The result is a concrete conditional composition theorem, not yet a full
graph-level runtime theorem. The original all-cost algorithm's binary weighted
reduction, actual encoded graph indexing, and implementation substitution must
still discharge those premises and the separate representation-cost bound.
-/
namespace DirectedFlowCutGap.BinaryWeightedPacking

open BinaryApproximatePacking BinaryApproximatePackingZeros
open BinaryApproximatePackingSampling BinaryApproximatePackingMarginal
open BinaryApproximatePackingProbability BinaryZeroAvoidingProvider
open BinaryFractionalRows BinaryRational
open scoped ENNReal

variable {m : ℕ}

/-- Actual data retained for the cost and full-metadata theorem. Every provider
failure/counter record remains in history.answers, including bad-cost outputs. -/
structure Output (w : Row m) (columns : Set (FractionalCover.Column m)) where
  history : InputResult (auxiliary w) (zeroFreeColumns w columns)
  selected : BinaryWeightedSampling.Result
  operations : ℕ

/-- Capacity fill is computed and charged once. The final history and sampler
charges are both retained; the last sample's charge is not the entire runtime. -/
def run {M : Type → Type} [Monad M] (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider M columns) (bit : M Bool) (fuel : BinaryArithmetic.Bits) :
    M (Output w columns) := do
  let filled := BinaryPositiveCapacities.prepare w
  let history ← solveInputM filled.1 (zeroFreeColumns w columns)
    (auxiliaryProvider w columns hS hempty draw)
  let selected ← BinaryWeightedSampling.sampleEvents bit history.rest.state.events fuel
  pure ⟨history,selected,filled.2+history.operations+selected.operations+8⟩

noncomputable section

/-- Projection preserves the actual complete sampler record. The provider
history and its charge remain available in the unprojected output. -/
theorem run_selected (w : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (fuel : BinaryArithmetic.Bits) :
    (run w columns hS hempty draw BinaryWeightedSamplingLaw.fairBit fuel).map
      Output.selected =
      sampleController w columns (auxiliaryProvider w columns hS hempty draw) fuel := by
  change ((solveInputM (auxiliary w) (zeroFreeColumns w columns)
      (auxiliaryProvider w columns hS hempty draw)).bind fun history =>
      (BinaryWeightedSampling.sampleEvents BinaryWeightedSamplingLaw.fairBit
        history.rest.state.events fuel).map (fun selected =>
          (⟨history,selected,(BinaryPositiveCapacities.prepare w).2 +
            history.operations + selected.operations + 8⟩ : Output w columns))).map
      Output.selected = _
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  exact congrArg (fun f => (solveInputM (auxiliary w) (zeroFreeColumns w columns)
    (auxiliaryProvider w columns hS hempty draw)).bind f)
    (funext fun history => PMF.map_id _)

theorem quality_failure_le (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α : ℝ) (ε : ℝ≥0∞)
    (hquery : (draw (BinaryZeroAvoidingSelector.prepare w c).costs).toOuterMeasure
      (BinaryZeroAvoidingProbability.queryFailure w
        (BinaryZeroAvoidingSelector.prepare w c).costs α) ≤ ε) :
    (auxiliaryProvider w columns hS hempty draw c).toOuterMeasure
      {a | ¬ OriginalQuality w α c a.1.choice} ≤ ε := by
  have h := BinaryZeroAvoidingProbability.auxiliaryProvider_failure_le
    w c columns hS hempty draw α ε hquery
  have he : {a : SafeAnswer (auxiliary w) (zeroFreeColumns w columns) |
      ¬ OriginalQuality w α c a.1.choice} =
      {a | a.1 ∈ BinaryZeroAvoidingProbability.outputFailure w c α} := by
    ext a
    simp only [Set.mem_ofPred_eq,OriginalQuality,
      BinaryZeroAvoidingProbability.outputFailure,
      BinaryZeroAvoidingProbability.answerCost_eq_length,
      BinaryZeroAvoidingProbability.potential_eq_objective,not_le]
  rw [he]
  exact h

/-- This sharper premise charges an absent cut only when its actual support
fallback is too costly. It therefore covers a harmless zero-objective `none`
branch without requiring an artificial success record from that branch. -/
theorem quality_failure_le_charged (w c : Row m)
    (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α : ℝ) (ε : ℝ≥0∞)
    (hcharged : (draw (BinaryZeroAvoidingSelector.prepare w c).costs).toOuterMeasure
      (BinaryZeroAvoidingProbability.chargedFailure w c α) ≤ ε) :
    (auxiliaryProvider w columns hS hempty draw c).toOuterMeasure
      {a | ¬ OriginalQuality w α c a.1.choice} ≤ ε := by
  have h := (BinaryZeroAvoidingProbability.auxiliaryProvider_failure_le_charged
    w c columns hS hempty draw α).trans hcharged
  have he : {a : SafeAnswer (auxiliary w) (zeroFreeColumns w columns) |
      ¬ OriginalQuality w α c a.1.choice} =
      {a | a.1 ∈ BinaryZeroAvoidingProbability.outputFailure w c α} := by
    ext a
    simp only [Set.mem_ofPred_eq,OriginalQuality,
      BinaryZeroAvoidingProbability.outputFailure,
      BinaryZeroAvoidingProbability.answerCost_eq_length,
      BinaryZeroAvoidingProbability.potential_eq_objective,not_le]
  rw [he]
  exact h

/-- The actual adaptive controller inherits the original provider's quality
at each actually formed penalized row. No physical flag is a quality test. -/
theorem bad_history_le (w : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (α ε : ℝ) (hε : 0 ≤ ε)
    (hcharged : ∀ c, (draw (BinaryZeroAvoidingSelector.prepare w c).costs).toOuterMeasure
      (BinaryZeroAvoidingProbability.chargedFailure w c α) ≤ ENNReal.ofReal ε) :
    ((solveInputM (auxiliary w) (zeroFreeColumns w columns)
      (auxiliaryProvider w columns hS hempty draw)).toOuterMeasure
        {r | ¬ OriginalBudget r α}).toReal ≤ (3*m^2+1 : ℕ)*ε := by
  apply originalBudget_failure_toReal_le w columns _ α ε hε
  intro c
  exact ENNReal.toReal_le_of_le_ofReal hε
    (quality_failure_le_charged w c columns hS hempty draw α _ (hcharged c))

/-- Original validity and zero avoidance hold on every returned outcome,
including provider failure and rejection-sampler exhaustion. -/
theorem run_valid (w : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (hm : 0 < m) (fuel : BinaryArithmetic.Bits)
    {out : Output w columns}
    (hout : out ∈ (run w columns hS hempty draw
      BinaryWeightedSamplingLaw.fairBit fuel).support) :
    ∃ q : Choice m, out.selected.label = some q.mask.toList ∧
      (BinaryFractionalCore.decodeChoice q).column ∈ columns ∧
      ∀ i ∈ (BinaryFractionalCore.decodeChoice q).column,
        0 < (decode (get w i)).value := by
  have hs : out.selected ∈ ((run w columns hS hempty draw
      BinaryWeightedSamplingLaw.fairBit fuel).map Output.selected).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨out,hout,rfl⟩
  rw [run_selected] at hs
  exact sampleController_valid w columns _ hm fuel hs

/-- A fixed polynomial number of adaptive queries and one finite weighted
selection give factor four after the separately explicit error split.
Original W, original coordinates, and supplied rational widths are unchanged.
-/
theorem run_marginal_four (w : Row m) (columns : Set (FractionalCover.Column m))
    (hS : SupportValid w columns) (hempty : (∅ : FractionalCover.Column m) ∉ columns)
    (draw : CutProvider PMF columns) (hm : 0 < m) (B : ℕ)
    (hwidth : ∀ i, (decode (get w i)).Bounded B)
    {α ε : ℝ} (hα : 0 < α) (hε : 0 ≤ ε)
    (hunit : 1 ≤ α * WeightedFailureBudget.totalWeight (fun i => decode (get w i)))
    (hcharged : ∀ c, (draw (BinaryZeroAvoidingSelector.prepare w c).costs).toOuterMeasure
      (BinaryZeroAvoidingProbability.chargedFailure w c α) ≤ ENNReal.ofReal ε)
    (fuel : BinaryArithmetic.Bits)
    (horacle : (3*m^2+1 : ℕ)*ε ≤ WeightedFailureBudget.tolerance m B/2)
    (hsampler : ((1 : ℝ)/2)^BinaryArithmetic.value fuel ≤
      WeightedFailureBudget.tolerance m B/2) (i : Fin m) :
    ((run w columns hS hempty draw BinaryWeightedSamplingLaw.fairBit fuel).toOuterMeasure {out | out.selected.label.any (coordinate i) = true}).toReal ≤
        4*α*(FractionalCover.value (capacities w) i : ℝ) := by
  have h := sampleController_marginal_four w columns
    (auxiliaryProvider w columns hS hempty draw) hm B hwidth hα
    (by positivity : 0 ≤ (3*m^2+1 : ℕ)*ε) hunit fuel
    (bad_history_le w columns hS hempty draw α ε hε hcharged) horacle hsampler i
  rw [← run_selected w columns hS hempty draw fuel,
    PMF.toOuterMeasure_map_apply] at h
  exact h

end
end DirectedFlowCutGap.BinaryWeightedPacking
