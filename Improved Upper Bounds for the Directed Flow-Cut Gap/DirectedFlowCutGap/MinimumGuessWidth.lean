import DirectedFlowCutGap.MinimumGuessProgram

namespace DirectedFlowCutGap.MinimumGuess
open BinaryArithmetic BinaryRational

theorem shifted_width {n : ℕ} (costs : BinaryFractionalRows.Row n) (i : Fin n) (exponent : Bits) :
    ∀ q∈(shifted costs i exponent).toList,StoredBounded q (shiftedWidth costs.toList exponent) := by
  have exactRow := ShiftedGridProgram.result_original costs i (RowVertices.vertexLabel i) exponent (RowVertices.label_numeric i)
  have valid : value (RowVertices.vertexLabel i)<costs.toList.length := by
    simp [RowVertices.label_numeric]
  have scalar := ShiftedGridProgram.scalar_width costs.toList (RowVertices.vertexLabel i) exponent valid
  intro q hq
  change q∈(BinaryFractionalGuesses.shifted costs
    (BinaryFractionalGuesses.lambda costs i (BinaryFractionalCore.dimension costs).1 exponent).1).1.toList at hq
  rw [← exactRow] at hq
  change q∈costs.toList.map (fun x => (BinaryRational.add x
    (ShiftedGridProgram.scalar costs.toList (RowVertices.vertexLabel i) exponent)).1) at hq
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hq
  have hb:=LambdaRowProgram.member_bits hx
  have xb : StoredBounded x (LambdaRowProgram.rowBits costs.toList) := ⟨by omega,by omega⟩
  exact add_stored_bounded (BinaryFractionalRows.stored_raw_bound xb) (BinaryFractionalRows.stored_raw_bound scalar)
end DirectedFlowCutGap.MinimumGuess
