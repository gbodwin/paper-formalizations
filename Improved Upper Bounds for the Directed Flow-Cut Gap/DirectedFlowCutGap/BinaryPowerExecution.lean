import DirectedFlowCutGap.BinaryPowerBound
namespace DirectedFlowCutGap.BinaryPowerProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem power {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 96)) (source : Bits) :
    ∃ ext root,ext.length=cells word ∧
      NaturalRun program (steps word+1) (state heap next a b c d stack source 94) []
        (state (heap++ext) (next+ext.length) a b c root stack source 95) ∧
      BoolList (heap++ext) root (BinaryCounters.powerOfTwoBinary word).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := power_return input next b c d dense ⟨a,b,c,d⟩ 95 stack source
  have first : tickNatural program (state heap next a b c d stack source 94)=
      some ⟨state heap next a b c d (⟨95,.r3,⟨a,b,c,d⟩⟩::stack) source 76,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩
end DirectedFlowCutGap.BinaryPowerProgram
