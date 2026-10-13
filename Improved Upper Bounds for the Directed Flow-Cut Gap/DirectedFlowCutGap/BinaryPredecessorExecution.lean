import DirectedFlowCutGap.BinaryPredecessorBound
namespace DirectedFlowCutGap.BinaryPredecessorProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem pred {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root,ext.length=cells word ∧
      NaturalRun program (steps word+1) (state heap next a b c d stack source 62) []
        (state (heap++ext) (next+ext.length) a b c root stack source 63) ∧
      BoolList (heap++ext) root (predecessor word).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := predecessor_return input next b c d dense ⟨a,b,c,d⟩ 63 stack source
  have first : tickNatural program (state heap next a b c d stack source 62)=
      some ⟨state heap next a b c d (⟨63,.r3,⟨a,b,c,d⟩⟩::stack) source 40,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩
end DirectedFlowCutGap.BinaryPredecessorProgram
