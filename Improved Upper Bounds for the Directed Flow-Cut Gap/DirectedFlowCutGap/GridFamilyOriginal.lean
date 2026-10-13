import DirectedFlowCutGap.GridFamilySpecification

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic

theorem values_original {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (costs : BinaryFractionalRows.Row n)
    (j : Fin n) (chosen : (BinaryFractionalDispatch.minimumPositive costs).1=some j)
    (exponent fuel : Bits) :
    values adjacency ds costs exponent fuel=
      ((BinaryFractionalGuesses.guessesFrom adjacency ds costs j
        (BinaryFractionalCore.dimension costs).1 exponent fuel).results).map (fun r => some r.state) := by
  induction exponent, fuel using instructionBound.induct with
  | case1 exponent fuel hz =>
    rw [values,BinaryFractionalGuesses.guessesFrom]
    simp [hz]
  | case2 exponent fuel hz ih =>
    rw [values,BinaryFractionalGuesses.guessesFrom]
    simp [hz,MinimumGuess.result,chosen,ih]

theorem values_length {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (costs : BinaryFractionalRows.Row n)
    (exponent fuel : Bits) : (values adjacency ds costs exponent fuel).length=value fuel := by
  induction exponent, fuel using instructionBound.induct with
  | case1 exponent fuel hz =>
    have hv := (isZero_spec fuel).1.mp hz
    rw [values];simp [hz,hv]
  | case2 exponent fuel hz ih =>
    have hv : 0<value fuel := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec fuel).1.mpr h))
    rw [values];simp only [dite_eq_right hz,List.length_cons,ih,(predecessor_spec fuel).1]
    omega
theorem values_none {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (costs : BinaryFractionalRows.Row n)
    (chosen : (BinaryFractionalDispatch.minimumPositive costs).1=none) (exponent fuel : Bits) :
    values adjacency ds costs exponent fuel=List.replicate (value fuel) none := by
  induction exponent, fuel using instructionBound.induct with
  | case1 exponent fuel hz =>
    have hv := (isZero_spec fuel).1.mp hz
    rw [values];simp [hz,hv]
  | case2 exponent fuel hz ih =>
    have hv : 0<value fuel := Nat.pos_of_ne_zero (fun h => hz ((isZero_spec fuel).1.mpr h))
    have size : value fuel=value (predecessor fuel).1+1 := by rw [(predecessor_spec fuel).1];omega
    rw [values]
    simp only [dite_eq_right hz,MinimumGuess.result,chosen,Option.map_none,ih]
    rw [size,List.replicate_succ]

end DirectedFlowCutGap.GridFamily
