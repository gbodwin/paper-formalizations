import DirectedFlowCutGap.BinaryApproximatePackingTrace
import DirectedFlowCutGap.BinaryPositiveCapacities

/-!
# Original zero coordinates in the actual retained packing events

The auxiliary capacities belong only to the controller. Columns below are the
original valid cuts restricted to avoid original zero coordinates. The final
cut, including any fallback, must already satisfy this condition before its
input-capacity bottleneck is selected. No threshold demand or original W is
formed from the auxiliary capacities. This bridge does not implement the cut
provider or its conditional good-event law.
-/
namespace DirectedFlowCutGap.BinaryApproximatePackingZeros
open scoped BigOperators NNRat
open BinaryApproximatePacking BinaryApproximatePackingTrace BinaryFractionalRows BinaryRational

variable {m : ℕ}

def zeroFreeColumns (w : Row m) (columns : Set (FractionalCover.Column m)) :
    Set (FractionalCover.Column m) :=
  {S | S ∈ columns ∧ ∀ i ∈ S, 0 < (decode (get w i)).value}

abbrev auxiliary (w : Row m) : Row m := (BinaryPositiveCapacities.prepare w).1

lemma auxiliary_positive (w : Row m) (i : Fin m) :
    0 < FractionalCover.value (capacities (auxiliary w)) i := by
  rw [capacities_value]
  change 0 < ((decode (get (auxiliary w) i)).value : ℚ)
  exact_mod_cast BinaryPositiveCapacities.positive w i

lemma auxiliary_value_selected (w : Row m) (i : Fin m)
    (hi : 0 < (decode (get w i)).value) :
    FractionalCover.value (capacities (auxiliary w)) i =
      FractionalCover.value (capacities w) i := by
  rw [capacities_value,capacities_value,BinaryPositiveCapacities.preserves_positive w i hi]

/-- The minimum is taken within the final selected original cut. A bottleneck
from an earlier, subsequently changed cut cannot supply these hypotheses. -/
theorem safe_auxiliary (w : Row m) (columns : Set (FractionalCover.Column m))
    (q : Choice m) (h : SafeChoice w (zeroFreeColumns w columns) q) :
    SafeChoice (auxiliary w) (zeroFreeColumns w columns) q := by
  refine ⟨h.1,h.2.1,?_⟩
  intro i hi
  rw [auxiliary_value_selected w q.bottleneck (h.1.2 _ h.2.1),
    auxiliary_value_selected w i (h.1.2 i hi)]
  exact h.2.2 i hi

/-- This is equality of the actual unreduced Fraction fields, including padding. -/
theorem event_original_amount {w : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : BinaryArithmetic.Bits}
    (r : StartedResult (auxiliary w) (zeroFreeColumns w columns) delta fuel)
    (e : Event m) (he : e ∈ r.rest.state.events) :
    e.amount = get w e.choice.bottleneck := by
  have hs := r.events_safe e he
  rw [hs.2]
  exact BinaryPositiveCapacities.preserves_positive w e.choice.bottleneck
    (hs.1.1.2 _ hs.1.2.1)

theorem event_original_valid {w : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : BinaryArithmetic.Bits}
    (r : StartedResult (auxiliary w) (zeroFreeColumns w columns) delta fuel)
    (e : Event m) (he : e ∈ r.rest.state.events) :
    (BinaryFractionalCore.decodeChoice e.choice).column ∈ columns ∧
      ∀ i ∈ (BinaryFractionalCore.decodeChoice e.choice).column,
        0 < (decode (get w i)).value := (r.events_safe e he).1.1

/-- Filling unused coordinates does not enlarge any retained amount's width. -/
theorem event_original_widths {w : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult (auxiliary w) (zeroFreeColumns w columns))
    (B : ℕ) (hw : ∀ i, StoredBounded (get w i) B) :
    r.rest.state.events.length ≤ 3*m^2 ∧
      ∀ e ∈ r.rest.state.events, StoredBounded e.amount B := by
  constructor
  · exact (r.events (B+1) (BinaryPositiveCapacities.stored w B hw)).1
  · intro e he
    rw [event_original_amount r e he]
    exact hw e.choice.bottleneck

theorem event_avoids_zero {w : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : BinaryArithmetic.Bits}
    (r : StartedResult (auxiliary w) (zeroFreeColumns w columns) delta fuel)
    (e : Event m) (he : e ∈ r.rest.state.events) (i : Fin m)
    (hi : (decode (get w i)).value=0) :
    i ∉ (BinaryFractionalCore.decodeChoice e.choice).column := by
  intro hmem
  have hp := (event_original_valid r e he).2 i hmem
  rw [hi] at hp
  exact lt_irrefl 0 hp

lemma state_events (s : State m) :
    (stateValue s).events = s.events.map (fun e =>
      FractionalCoverRawCore.decodeEvent (BinaryFractionalCore.decodeEvent e)) := by
  simp only [stateValue,FractionalCoverRawCore.decodeState,
    BinaryFractionalCore.decodeState,List.map_map,Function.comp_def]

/-- Zero-coordinate exclusion is unconditional, including cost-bad traces. -/
theorem traceLoad_zero {w : Row m} {columns : Set (FractionalCover.Column m)}
    {delta : Fraction} {fuel : BinaryArithmetic.Bits}
    (r : StartedResult (auxiliary w) (zeroFreeColumns w columns) delta fuel)
    (i : Fin m) (hi : (decode (get w i)).value=0) :
    FractionalCover.traceLoad (stateValue r.rest.state).events i=0 := by
  rw [state_events]
  unfold FractionalCover.traceLoad
  rw [List.map_map]
  apply List.sum_eq_zero
  intro q hq
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hq
  simp [FractionalCoverRawCore.decodeEvent,BinaryFractionalCore.decodeEvent,
    event_avoids_zero r e he i hi]

lemma objective_le_auxiliary (w : Row m) (y : FractionalCover.Row m)
    (hy : ∀ i, 0 ≤ FractionalCover.value y i) :
    FractionalCover.objective (capacities w) y ≤
      FractionalCover.objective (capacities (auxiliary w)) y := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hy i)
  rw [capacities_value,capacities_value]
  change ((decode (get w i)).value : ℚ) ≤ ((decode (get (auxiliary w) i)).value : ℚ)
  exact_mod_cast BinaryPositiveCapacities.original_le w i

lemma pathwise_positive (w : Row m) (oracle : ℕ → FractionalCover.Oracle m)
    (hm : 0 < m) (k : ℕ) :
    ∀ i, 0 < FractionalCover.value
      (ApproximatePackingTrace.run (capacities (auxiliary w)) oracle k).weights i := by
  induction k with
  | zero => exact FractionalCover.initial_pos _ hm (auxiliary_positive w)
  | succ k ih =>
      by_cases hs : 1 ≤ FractionalCover.objective (capacities (auxiliary w))
          (ApproximatePackingTrace.run (capacities (auxiliary w)) oracle k).weights
      · simpa only [ApproximatePackingTrace.run,FractionalCover.step,ite_eq_left hs] using ih
      · simpa only [ApproximatePackingTrace.run,FractionalCover.step,ite_eq_right hs] using
          FractionalCover.update_pos (capacities (auxiliary w)) _ _ (auxiliary_positive w) ih

/-- The cost premise uses the original input weights. Alpha, original graph n,
and original resource mass W remain external proof parameters unchanged by fill. -/
def OriginalBudget {w : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult (auxiliary w) (zeroFreeColumns w columns)) (α : ℝ) : Prop :=
  ∀ k<r.answers.length,
    let s := ApproximatePackingTrace.run (capacities (auxiliary w)) (oracleAt r) k
    FractionalCover.objective (capacities (auxiliary w)) s.weights < 1 →
      (FractionalCover.length s.weights (BinaryFractionalCore.decodeChoice (choiceAt r k)).column : ℝ)
        ≤ α*(FractionalCover.objective (capacities w) s.weights : ℝ)

/-- Weaken the original oracle guarantee only after it has been established at
the actual reached query state; auxiliary capacities never enter that oracle. -/
theorem originalBudget_to_good {w : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult (auxiliary w) (zeroFreeColumns w columns)) (hm : 0 < m)
    (α : ℝ) (hα : 0 ≤ α) (hb : OriginalBudget r α) : GoodBudget r α := by
  intro k hk
  dsimp only
  intro ha
  have hp := pathwise_positive w (oracleAt r) hm k
  have hle := objective_le_auxiliary w
    (ApproximatePackingTrace.run (capacities (auxiliary w)) (oracleAt r) k).weights
    (fun i => (hp i).le)
  exact (hb k hk ha).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hα)

/-- The final original-coordinate bound has a positive denominator. On an
original zero coordinate its numerator is exactly zero on every trace. -/
theorem original_marginal_le {w : Row m} {columns : Set (FractionalCover.Column m)}
    (r : InputResult (auxiliary w) (zeroFreeColumns w columns)) (hm : 0 < m)
    {α : ℝ} (hα : 0<α) (hb : OriginalBudget r α) (i : Fin m) :
    0 < FractionalCover.traceTotal (stateValue r.rest.state).events ∧
      (FractionalCover.traceLoad (stateValue r.rest.state).events i : ℝ) /
        (FractionalCover.traceTotal (stateValue r.rest.state).events : ℝ) ≤
          3*α*(FractionalCover.value (capacities w) i : ℝ) := by
  have h := retained_marginal_le r hm (auxiliary_positive w) hα
    (originalBudget_to_good r hm α hα.le hb) i
  refine ⟨h.1,?_⟩
  by_cases hi : (decode (get w i)).value=0
  · rw [traceLoad_zero r i hi,capacities_value]
    simp [FractionalCoverRawCore.rational,hi]
  · have hp : 0 < (decode (get w i)).value := lt_of_le_of_ne (by positivity) (Ne.symm hi)
    rw [auxiliary_value_selected w i hp] at h
    exact h.2

end DirectedFlowCutGap.BinaryApproximatePackingZeros
