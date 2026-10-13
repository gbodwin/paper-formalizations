import DirectedFlowCutGap.GridFamilyData

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic

/-- Proof-side output specification for the literal binary loop. -/
def values {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (costs : BinaryFractionalRows.Row n)
    (exponent fuel : Bits) : List (Option (BinaryFractionalCore.State n)) :=
  if _hz : (isZero fuel).1=true then [] else
    MinimumGuess.result adjacency ds costs exponent::
      values adjacency ds costs (increment true exponent).1 (predecessor fuel).1
termination_by value fuel
decreasing_by
  have hv : 0<value fuel := Nat.pos_of_ne_zero (fun h => _hz ((isZero_spec fuel).1.mpr h))
  rw [(predecessor_spec fuel).1]
  omega

/-- Only original rows, demand length and loop words occur in this envelope. -/
def instructionBound (d : ℕ) (rows : List BinaryRational.Fraction) (exponent fuel : Bits) : ℕ :=
  if _hz : (isZero fuel).1=true then BinaryZeroProgram.steps fuel+16 else
    BinaryZeroProgram.steps fuel+MinimumGuess.inputSteps d rows exponent+
      BinaryIncrementProgram.steps exponent+BinaryPredecessorProgram.steps fuel+
      instructionBound d rows (increment true exponent).1 (predecessor fuel).1+64
termination_by value fuel
decreasing_by
  have hv : 0<value fuel := Nat.pos_of_ne_zero (fun h => _hz ((isZero_spec fuel).1.mpr h))
  rw [(predecessor_spec fuel).1]
  omega
end DirectedFlowCutGap.GridFamily
