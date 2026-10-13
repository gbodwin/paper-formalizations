import DirectedFlowCutGap.BinaryLengthProgram
import DirectedFlowCutGap.BinaryCounters

namespace DirectedFlowCutGap.BinarySizeProgram
open BinaryArithmetic

theorem countWord_succ (n : ℕ) (acc : Bits) :
    BinaryLengthProgram.countWord (n+1) acc =
      (increment true (BinaryLengthProgram.countWord n acc)).1 := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simpa only [BinaryLengthProgram.countWord] using ih (increment true acc).1

theorem countWord_exact (word : Bits) :
    BinaryLengthProgram.countWord word.length [] = (BinaryCounters.lengthBits word).1 := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    simp only [List.length_cons,countWord_succ,ih,BinaryCounters.lengthBits]

end DirectedFlowCutGap.BinarySizeProgram
