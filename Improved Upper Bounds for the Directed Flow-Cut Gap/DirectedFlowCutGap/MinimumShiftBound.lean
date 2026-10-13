import DirectedFlowCutGap.MinimumShiftCalls

namespace DirectedFlowCutGap.MinimumShift
open BinaryArithmetic BinaryRational

theorem result_selected {n : ℕ} (costs : BinaryFractionalRows.Row n) (exponent : Bits) :
    result costs exponent=(OriginalRowMinimum.result costs.toList).map
      (fun x => ShiftedGridProgram.result costs.toList x.1 exponent) := by
  rw [OriginalRowMinimum.result_original]
  simp [result,Option.map_map,Function.comp_def]

theorem shift_envelope (rows : List Fraction) (index exponent : Bits) (width : index.length≤rows.length) :
    ShiftedGridProgram.inputSteps rows index exponent ≤
      ShiftedGridProgram.inputSteps rows (List.replicate rows.length false) exponent := by
  unfold ShiftedGridProgram.inputSteps LambdaGridProgram.inputSteps LambdaGridProgram.inputSize
  simp only [List.length_replicate]
  gcongr
end DirectedFlowCutGap.MinimumShift
