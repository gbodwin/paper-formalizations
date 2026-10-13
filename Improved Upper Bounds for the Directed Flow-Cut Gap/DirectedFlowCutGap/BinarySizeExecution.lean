import DirectedFlowCutGap.BinarySizeTrace

namespace DirectedFlowCutGap.BinarySizeProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def inputSteps (word : Bits) : ℕ := 32*(word.length+1)^2

theorem steps_bound (word : Bits) : steps word+1 ≤ inputSteps word := by
  have ht := BinaryTrimProgram.steps_bound word
  have hl := BinaryLengthProgram.scanSteps_bound (trim word).1.length []
  have len := (trim_spec word).2.2.1
  simp only [List.length_nil,Nat.zero_add] at hl
  have hm : (8*(trim word).1.length+12)*(trim word).1.length ≤
      (8*word.length+12)*word.length := Nat.mul_le_mul (by omega) len
  unfold steps inputSteps
  nlinarith

theorem size {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (stack : List (Frame ℕ 48)) (source : Bits) :
    ∃ ext root,ext.length=cells word ∧
      NaturalRun program (steps word+1) (state heap next a b c d stack source 46) []
        (state (heap++ext) (next+ext.length) a b c root stack source 47) ∧
      BoolList (heap++ext) root (BinaryCounters.sizeBits word).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := size_return input next b c d hn ⟨a,b,c,d⟩ 47 stack source
  have first : tickNatural program (state heap next a b c d stack source 46)=
      some ⟨state heap next a b c d (⟨47,.r3,⟨a,b,c,d⟩⟩::stack) source 38,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩
end DirectedFlowCutGap.BinarySizeProgram
