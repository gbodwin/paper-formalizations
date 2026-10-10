import DirectedFlowCutGap.BinaryApproximatePackingZeros
import DirectedFlowCutGap.BinaryWeightedSamplingLaw

/-!
# The retained packing amounts in the actual sampler's event law

Only a fixed returned history is conditioned on here. This bridge equates the
sampler's literal input amounts with the exact decoded retained event loads and
total, and interprets the selected full mask. It does not supply the probability
of a good controller history or a fresh-choice provider theorem.
-/
namespace DirectedFlowCutGap.BinaryApproximatePackingSampling
open scoped NNRat ENNReal
open BinaryApproximatePacking BinaryApproximatePackingZeros BinaryFractionalRows BinaryRational

variable {m : ℕ}

def coordinate (i : Fin m) (bits : BinaryArithmetic.Bits) : Bool := bits.getD i.val false

lemma coordinate_mask (i : Fin m) (mask : Vector Bool m) :
    coordinate i mask.toList=mask[i.val] := by
  simp [coordinate,List.getD_eq_getElem?_getD,i.isLt]

lemma coordinate_choice (i : Fin m) (q : Choice m) :
    coordinate i q.mask.toList=true ↔ i ∈ (BinaryFractionalCore.decodeChoice q).column := by
  rw [coordinate_mask]
  simp [BinaryFractionalCore.decodeChoice,BinaryFractionalRows.column]

def decodedEvents (es : List (Event m)) : List (FractionalCover.Event m) :=
  es.map fun e => FractionalCoverRawCore.decodeEvent (BinaryFractionalCore.decodeEvent e)

lemma state_decodedEvents (s : State m) : (stateValue s).events=decodedEvents s.events :=
  state_events s

lemma decoded_total (es : List (Event m)) :
    FractionalCover.traceTotal (decodedEvents es)=eventTotal es := by
  simp [FractionalCover.traceTotal,decodedEvents,eventTotal,List.map_map,
    FractionalCoverRawCore.decodeEvent,BinaryFractionalCore.decodeEvent,Function.comp_def]

/-- The common-denominator construction retains exactly the event mass total. -/
theorem input_total (es : List (Event m)) :
    RawWeightedMasses.selectedValue
      (BinaryWeightedMasses.inputData (BinaryWeightedSampling.eventInput es).1) (fun _ => true) =
      (FractionalCover.traceTotal (decodedEvents es) : ℝ) := by
  rw [BinaryWeightedSampling.eventInput_value]
  induction es with
  | nil => simp [RawWeightedMasses.selectedValue,BinaryWeightedMasses.inputData,
      FractionalCover.traceTotal,decodedEvents]
  | cons e es ih =>
      simpa [RawWeightedMasses.selectedValue,BinaryWeightedMasses.inputData,
        FractionalCover.traceTotal,decodedEvents,FractionalCoverRawCore.decodeEvent,
        BinaryFractionalCore.decodeEvent,FractionalCoverRawCore.rational] using
        congrArg (fun x : ℝ => ((decode e.amount).value : ℝ)+x) ih

/-- Duplicate masks add their original amounts, exactly as traceLoad does. -/
theorem input_coordinate (es : List (Event m)) (i : Fin m) :
    RawWeightedMasses.selectedValue
      (BinaryWeightedMasses.inputData (BinaryWeightedSampling.eventInput es).1) (coordinate i) =
      (FractionalCover.traceLoad (decodedEvents es) i : ℝ) := by
  rw [BinaryWeightedSampling.eventInput_value]
  induction es with
  | nil => simp [RawWeightedMasses.selectedValue,BinaryWeightedMasses.inputData,
      FractionalCover.traceLoad,decodedEvents]
  | cons e es ih =>
      have hh : (if coordinate i e.choice.mask.toList then ((decode e.amount).value : ℝ) else 0) =
          ((if i ∈ (BinaryFractionalCore.decodeChoice e.choice).column then
            FractionalCoverRawCore.rational (decode e.amount) else 0 : ℚ) : ℝ) := by
        by_cases hi : i ∈ (BinaryFractionalCore.decodeChoice e.choice).column
        · have hm := (coordinate_choice i e.choice).mpr hi
          simp [hm,hi,FractionalCoverRawCore.rational]
        · have hm : coordinate i e.choice.mask.toList=false := Bool.eq_false_iff.mpr
            (fun h => hi ((coordinate_choice i e.choice).mp h))
          simp [hm,hi]
      simpa [RawWeightedMasses.selectedValue,BinaryWeightedMasses.inputData,
        FractionalCover.traceLoad,decodedEvents,FractionalCoverRawCore.decodeEvent,
        BinaryFractionalCore.decodeEvent] using congrArg₂ (·+·) hh ih

noncomputable section

/-- One actual fair-bit selection from a fixed retained history. The additive
term is the sampler's proved bounded-rejection error, not an uncharged oracle. -/
theorem retained_sample_event_le (es : List (Event m)) (fuel : BinaryArithmetic.Bits)
    (positive : 0<eventTotal es) (i : Fin m) :
    ((BinaryWeightedSampling.sampleEvents BinaryWeightedSamplingLaw.fairBit es fuel).toOuterMeasure
      {r | r.label.any (coordinate i)=true}).toReal ≤
        (FractionalCover.traceLoad (decodedEvents es) i : ℝ) /
          (eventTotal es : ℝ)+((1 : ℝ)/2)^BinaryArithmetic.value fuel := by
  have hp : 0<RawWeightedMasses.selectedValue
      (BinaryWeightedMasses.inputData (BinaryWeightedSampling.eventInput es).1) (fun _ => true) := by
    rw [input_total,decoded_total]
    exact_mod_cast positive
  have h := BinaryWeightedSamplingLaw.sampleEvents_event_le es fuel (coordinate i) hp
  simpa only [input_coordinate,input_total,decoded_total] using h

/-- Original-zero support exclusion holds under every bit law, on every
structurally valid returned trace, including cost-bad provider outcomes. -/
theorem original_zero_event {w : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {budget : BinaryArithmetic.Bits}
    (r : StartedResult (auxiliary w) (zeroFreeColumns w columns) delta budget)
    (bit : PMF Bool) (fuel : BinaryArithmetic.Bits) (i : Fin m)
    (hi : (decode (get w i)).value=0) :
    (BinaryWeightedSampling.sampleEvents bit r.rest.state.events fuel).toOuterMeasure
      {out | out.label.any (coordinate i)=true} = 0 := by
  apply BinaryWeightedSamplingLaw.sampleEvents_event_zero
  intro e he
  apply Bool.eq_false_iff.mpr
  intro h
  exact event_avoids_zero r e he i hi ((coordinate_choice i e.choice).mp h)

/-- Conditional on original-weight cost budgets at the actual reached states,
the real sampler has the original-coordinate marginal guarantee. The separate
probability of violating those budgets is still an adaptive-history obligation. -/
theorem original_good_event_le {w : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult (auxiliary w) (zeroFreeColumns w columns)) (hm : 0 < m)
    {α : ℝ} (hα : 0<α) (hb : OriginalBudget r α)
    (fuel : BinaryArithmetic.Bits) (i : Fin m) :
    ((BinaryWeightedSampling.sampleEvents BinaryWeightedSamplingLaw.fairBit r.rest.state.events fuel).toOuterMeasure
      {out | out.label.any (coordinate i)=true}).toReal ≤
        3*α*(FractionalCover.value (capacities w) i : ℝ)+
          ((1 : ℝ)/2)^BinaryArithmetic.value fuel := by
  have hp := (r.total_positive hm (auxiliary_positive w)).1
  have hs := retained_sample_event_le r.rest.state.events fuel hp i
  have hmarg := (original_marginal_le r hm hα hb i).2
  rw [state_decodedEvents,decoded_total] at hmarg
  exact hs.trans (add_le_add hmarg le_rfl)

end
end DirectedFlowCutGap.BinaryApproximatePackingSampling
