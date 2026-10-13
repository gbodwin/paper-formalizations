import DirectedFlowCutGap.BinaryPredecessorTrace
namespace DirectedFlowCutGap.BinaryPredecessorProgram
open BinaryArithmetic

def inputSteps (word : Bits) : ℕ := 24*word.length+32

theorem steps_bound (word : Bits) : steps word+1 ≤ inputSteps word := by
  have hz := BinaryZeroProgram.steps_bound word
  have hb := BinaryBorrowProgram.steps_bound word
  have ht := BinaryTrimProgram.steps_bound (predCore word).1
  have hp := (predCore_spec word).2.1
  unfold steps inputSteps
  split <;> omega

theorem cells_bound (word : Bits) : cells word ≤ 3*word.length+4 := by
  have hb := BinaryBorrowProgram.cells_bound word
  have ht := (trim_spec (predCore word).1).2.2.1
  have hp := (predCore_spec word).2.1
  unfold cells
  split <;> omega
end DirectedFlowCutGap.BinaryPredecessorProgram
