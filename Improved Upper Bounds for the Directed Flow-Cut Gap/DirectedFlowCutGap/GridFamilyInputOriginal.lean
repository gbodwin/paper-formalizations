import DirectedFlowCutGap.GridFamilyInputProgram

namespace DirectedFlowCutGap.GridFamilyInput
open BinaryArithmetic

theorem fuel_original {n : ℕ} (costs : BinaryFractionalRows.Row n) :
    fuel costs.toList=(BinaryFractionalGuesses.gridFuel (BinaryFractionalCore.dimension costs).1
      (BinaryFractionalGuesses.inputWidth costs).1).1 := by
  simp only [fuel,GridInputProgram.dimension_exact,GridInputProgram.width,BinaryFractionalGuesses.inputWidth]

theorem values_original {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) (costs : BinaryFractionalRows.Row n)
    (j : Fin n) (chosen : (BinaryFractionalDispatch.minimumPositive costs).1=some j) :
    GridFamily.values adjacency ds costs [] (fuel costs.toList)=
      ((BinaryFractionalGuesses.guesses adjacency ds costs j
        (BinaryFractionalGuesses.inputWidth costs).1).results).map (fun r => some r.state) := by
  rw [GridFamily.values_original adjacency ds costs j chosen,fuel_original]
  rfl
end DirectedFlowCutGap.GridFamilyInput
