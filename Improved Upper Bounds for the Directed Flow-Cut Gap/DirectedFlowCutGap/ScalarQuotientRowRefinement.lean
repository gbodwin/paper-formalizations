import DirectedFlowCutGap.ActualScalarQuotientRow

namespace DirectedFlowCutGap.ScalarQuotientRow
open BinaryRational

theorem row_toList {m : ℕ} (xs : BinaryFractionalRows.Row m) :
    xs.toList=List.ofFn (fun i : Fin m => BinaryFractionalRows.get xs i) := by
  rw [←Vector.toList_ofFn]
  congr
  ext i hi
  simp [BinaryFractionalRows.get]

/-- The scalar-numerator mode is literally the old initialization row. -/
theorem result_eq_initial {m : ℕ} (c : BinaryFractionalRows.Row m) (delta : Fraction) :
    result true delta c.toList=(BinaryFractionalRows.initial c delta).1.toList := by
  simp [result,numerator,denominator,BinaryFractionalRows.initial,
    EncodedRoundingInput.tabulate_value,row_toList,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]

/-- This is only the final scalar-division stage. The masked length must still
be constructed by the calling controller before this theorem is instantiated. -/
theorem result_eq_normalized {m : ℕ} (y : BinaryFractionalRows.Row m) (mask : Vector Bool m) :
    result false (BinaryFractionalRows.length y mask).1 y.toList=
      (BinaryFractionalRows.normalized y mask).1.toList := by
  simp [result,numerator,denominator,BinaryFractionalRows.normalized,
    EncodedRoundingInput.tabulate_value,row_toList,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]
end DirectedFlowCutGap.ScalarQuotientRow
