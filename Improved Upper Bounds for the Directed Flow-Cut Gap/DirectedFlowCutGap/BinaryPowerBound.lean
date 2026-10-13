import DirectedFlowCutGap.BinaryPowerTrace
namespace DirectedFlowCutGap.BinaryPowerProgram
open BinaryArithmetic

/-- Numeric exponent is explicit: output length is value(word)+1. -/
def inputSteps (word : Bits) : ℕ := 64*(value word+1)*(word.length+1)

theorem steps_bound (word : Bits) : steps word+1 ≤ inputSteps word := by
  induction word using steps.induct with
  | case1 word hz =>
    have hv := (isZero_spec word).1.mp hz
    have hzsteps := BinaryZeroProgram.steps_bound word
    rw [steps]
    simp [hz,inputSteps,hv]
    omega
  | case2 word hz ih =>
    have hv : 0<value word := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec word).1.mpr h))
    have hp := (predecessor_spec word).1
    have hl := ImmutableReferenceSimulation.predecessor_width word
    have hzsteps := BinaryZeroProgram.steps_bound word
    have hpsteps := BinaryPredecessorProgram.steps_bound word
    have mono := Nat.mul_le_mul_left (64*(value word)) (Nat.add_le_add_right hl 1)
    unfold inputSteps at ih
    have eq : value (predecessor word).1+1=value word := by omega
    rw [eq] at ih
    rw [steps]
    simp [hz]
    unfold inputSteps BinaryPredecessorProgram.inputSteps at *
    nlinarith
end DirectedFlowCutGap.BinaryPowerProgram
