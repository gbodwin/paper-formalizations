import DirectedFlowCutGap.BinaryApproximatePackingSampling
import DirectedFlowCutGap.WeightedMixtureBound
import DirectedFlowCutGap.WeightedFailureBudget

/-!
# Unconditional marginals of the actual controller and weighted sampler

The executable probability law below is the bind of the actual cached
controller with its actual finite-bit weighted sampler. The construction
history is unrestricted; no finite instance for rational rows, masks, or
retained histories is introduced. The controller's bad-budget probability
remains an explicit premise until the adaptive provider theorem is applied.

Original zero coordinates are excluded on every history, including cost-bad
histories and physical failure fallbacks. Positive coordinates absorb the two
separately bounded errors using the original weights and original total W.
Neither alpha nor a normalized replacement for W appears in the program.
-/
namespace DirectedFlowCutGap.BinaryApproximatePackingMarginal

open BinaryApproximatePacking BinaryApproximatePackingZeros
open BinaryApproximatePackingSampling BinaryFractionalRows BinaryRational
open scoped ENNReal

noncomputable section

variable {m : ℕ}

lemma probability_ne_top {A : Type*} (p : PMF A) (event : Set A) :
    p.toOuterMeasure event ≠ ⊤ :=
  (lt_of_le_of_lt (WeightedMixtureBound.event_le_one p event) (by simp)).ne

/-- The real-valued form keeps the actual bad-history mass; it does not
condition the original law on an event that depends on the output. -/
theorem bind_event_toReal_le {A B : Type*} (p : PMF A) (next : A → PMF B)
    (good : A → Prop) (event : Set B) (bound error : ℝ)
    (hb : 0 ≤ bound) (he : 0 ≤ error)
    (hgood : ∀ a ∈ p.support, good a →
      ((next a).toOuterMeasure event).toReal ≤ bound)
    (hbad : (p.toOuterMeasure {a | ¬ good a}).toReal ≤ error) :
    ((p.bind next).toOuterMeasure event).toReal ≤ bound + error := by
  have hg : ∀ a ∈ p.support, good a →
      (next a).toOuterMeasure event ≤ ENNReal.ofReal bound := by
    intro a ha hg
    have h := ENNReal.ofReal_le_ofReal (hgood a ha hg)
    rwa [ENNReal.ofReal_toReal (probability_ne_top (next a) event)] at h
  have hd : p.toOuterMeasure {a | ¬ good a} ≤ ENNReal.ofReal error := by
    have h := ENNReal.ofReal_le_ofReal hbad
    rwa [ENNReal.ofReal_toReal (probability_ne_top p _)] at h
  have h := (WeightedMixtureBound.bind_event_le p next good event
    (ENNReal.ofReal bound) hg).trans (add_le_add le_rfl hd)
  rw [← ENNReal.ofReal_add hb he] at h
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg hb he) h

/-- One actual history is generated, followed by one actual weighted draw.
The caller's provider must still have its implementation and quality laws. -/
def sampleController (w : Row m) (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF (auxiliary w) (zeroFreeColumns w columns))
    (fuel : BinaryArithmetic.Bits) : PMF BinaryWeightedSampling.Result :=
  (solveInputM (auxiliary w) (zeroFreeColumns w columns) draw).bind fun r =>
    BinaryWeightedSampling.sampleEvents BinaryWeightedSamplingLaw.fairBit
      r.rest.state.events fuel

/-- This bound is unconditional. It uses the actual controller's bad-budget
mass, with no independence premise between its history and continuation. -/
theorem sampleController_event_le (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF (auxiliary w) (zeroFreeColumns w columns))
    (hm : 0 < m) {α error : ℝ} (hα : 0 < α) (he : 0 ≤ error)
    (fuel : BinaryArithmetic.Bits)
    (hbad : ((solveInputM (auxiliary w) (zeroFreeColumns w columns) draw).toOuterMeasure {r | ¬ OriginalBudget r α}).toReal ≤ error) (i : Fin m) :
    ((sampleController w columns draw fuel).toOuterMeasure
      {out | out.label.any (coordinate i) = true}).toReal ≤
        3*α*(FractionalCover.value (capacities w) i : ℝ) +
          ((1 : ℝ)/2)^BinaryArithmetic.value fuel + error := by
  have hw : 0 ≤ (FractionalCover.value (capacities w) i : ℝ) := by
    rw [capacities_value]
    change 0 ≤ ((decode (get w i)).value : ℝ)
    positivity
  apply bind_event_toReal_le _ _ (fun r => OriginalBudget r α) _ _ error
    (by positivity) he _ hbad
  intro r _hr hg
  exact original_good_event_le r hm hα hg fuel i

/-- Original zero coordinates have probability exactly zero, even when the
provider or finite rejection sampler takes a fallback branch. -/
theorem sampleController_event_zero (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF (auxiliary w) (zeroFreeColumns w columns))
    (fuel : BinaryArithmetic.Bits) (i : Fin m)
    (hi : (decode (get w i)).value = 0) :
    (sampleController w columns draw fuel).toOuterMeasure
      {out | out.label.any (coordinate i) = true} = 0 := by
  apply WeightedMixtureBound.bind_event_zero
  intro r _hr
  exact original_zero_event r BinaryWeightedSamplingLaw.fairBit fuel i hi

lemma original_weight (w : Row m) (i : Fin m) :
    WeightedFailureBudget.weight (decode (get w i)) =
      (FractionalCover.value (capacities w) i : ℝ) := by
  rw [WeightedFailureBudget.weight_eq_value,capacities_value]
  rfl

/-- A positive event total forces an actual retained mask on every supported
outcome, including exhausted rejection sampling with a legal default ticket. -/
theorem sampleEvents_member (bit : PMF Bool) (es : List (Event m))
    (fuel : BinaryArithmetic.Bits) (positive : 0 < eventTotal es)
    {out : BinaryWeightedSampling.Result}
    (hout : out ∈ (BinaryWeightedSampling.sampleEvents bit es fuel).support) :
    ∃ e ∈ es, out.label = some e.choice.mask.toList := by
  have hp : 0 < RawWeightedMasses.selectedValue
      (BinaryWeightedMasses.inputData (BinaryWeightedSampling.eventInput es).1)
      (fun _ => true) := by
    rw [input_total,decoded_total]
    exact_mod_cast positive
  have ht := BinaryWeightedSamplingLaw.prepare_positive
    (BinaryWeightedSampling.eventInput es).1 hp
  obtain ⟨a,ha,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  obtain ⟨r,hr,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hb
  rw [BinaryBoundedSampler.checkedDrawCharged] at hr
  split at hr
  next hz =>
    have hv := (BinaryArithmetic.isZero_spec
      (BinaryWeightedSampling.prepare (BinaryWeightedSampling.eventInput es).1).total).1.mp hz
    omega
  next hn =>
    obtain ⟨ticket,_hq,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
    have he := (PMF.mem_support_pure_iff _ _).mp hr
    subst r
    obtain ⟨e,he,hl,_hlen⟩ := BinaryWeightedSampling.finish_event es ticket
      ((BinaryArithmetic.isZero
        (BinaryWeightedSampling.prepare (BinaryWeightedSampling.eventInput es).1).total).2 +
        ticket.steps + 8)
    exact ⟨e,he,hl⟩

/-- Actual output validity is independent of good cost budgets. The full mask
belongs to an original valid cut and avoids every original zero coordinate. -/
theorem sampleController_valid (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF (auxiliary w) (zeroFreeColumns w columns))
    (hm : 0 < m) (fuel : BinaryArithmetic.Bits)
    {out : BinaryWeightedSampling.Result}
    (hout : out ∈ (sampleController w columns draw fuel).support) :
    ∃ q : Choice m, out.label = some q.mask.toList ∧
      (BinaryFractionalCore.decodeChoice q).column ∈ columns ∧
      ∀ i ∈ (BinaryFractionalCore.decodeChoice q).column,
        0 < (decode (get w i)).value := by
  obtain ⟨r,_hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have hp := (r.total_positive hm (auxiliary_positive w)).1
  obtain ⟨e,he,hl⟩ := sampleEvents_member BinaryWeightedSamplingLaw.fairBit
    r.rest.state.events fuel hp hout
  have hs := (r.events_safe e he).1.1
  exact ⟨e.choice,hl,hs.1,hs.2⟩

/-- Both halves are measured relative to the unchanged original weight
encoding. This absorbs the additive error with a universal constant four,
including alpha below one and original coordinates of weight zero. -/
theorem sampleController_marginal_four (w : Row m)
    (columns : Set (FractionalCover.Column m))
    (draw : Oracle PMF (auxiliary w) (zeroFreeColumns w columns))
    (hm : 0 < m) (B : ℕ)
    (hwidth : ∀ i, (decode (get w i)).Bounded B)
    {α error : ℝ} (hα : 0 < α) (he : 0 ≤ error)
    (hunit : 1 ≤ α * WeightedFailureBudget.totalWeight (fun i => decode (get w i)))
    (fuel : BinaryArithmetic.Bits)
    (hbad : ((solveInputM (auxiliary w) (zeroFreeColumns w columns) draw).toOuterMeasure {r | ¬ OriginalBudget r α}).toReal ≤ error)
    (horacle : error ≤ WeightedFailureBudget.tolerance m B / 2)
    (hsampler : ((1 : ℝ)/2)^BinaryArithmetic.value fuel ≤
      WeightedFailureBudget.tolerance m B / 2) (i : Fin m) :
    ((sampleController w columns draw fuel).toOuterMeasure
      {out | out.label.any (coordinate i) = true}).toReal ≤
        4*α*(FractionalCover.value (capacities w) i : ℝ) := by
  by_cases hi : (decode (get w i)).value = 0
  · rw [sampleController_event_zero w columns draw fuel i hi]
    rw [← original_weight,WeightedFailureBudget.weight_eq_value,hi]
    simp
  · have hpos : 0 < WeightedFailureBudget.weight (decode (get w i)) := by
      rw [WeightedFailureBudget.weight_eq_value]
      exact_mod_cast lt_of_le_of_ne (by positivity : 0 ≤ (decode (get w i)).value)
        (Ne.symm hi)
    have ht := WeightedFailureBudget.tolerance_le_scaled_weight
      (fun i => decode (get w i)) B hwidth hα.le hunit i hpos
    simp only [Fintype.card_fin,original_weight] at ht
    have hp := sampleController_event_le w columns draw hm hα he fuel hbad i
    linarith

end
end DirectedFlowCutGap.BinaryApproximatePackingMarginal
