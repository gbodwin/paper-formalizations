import DirectedFlowCutGap.ActualScalarAdditionRow
import DirectedFlowCutGap.BinaryFractionalGuesses

namespace DirectedFlowCutGap.ScalarAdditionRow
open BinaryRational

theorem row_toList {m : ℕ} (xs : BinaryFractionalRows.Row m) :
    xs.toList=List.ofFn (fun i : Fin m => BinaryFractionalRows.get xs i) := by
  rw [←Vector.toList_ofFn]
  congr
  ext i hi
  simp [BinaryFractionalRows.get]

/-- Every returned row entry is exactly the original unreduced c+lambda. -/
theorem result_eq_shifted {m : ℕ} (c : BinaryFractionalRows.Row m) (scalar : Fraction) :
    result scalar c.toList=(BinaryFractionalGuesses.shifted c scalar).1.toList := by
  simp [result,BinaryFractionalGuesses.shifted,EncodedRoundingInput.tabulate_value,
    row_toList,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]
end DirectedFlowCutGap.ScalarAdditionRow
