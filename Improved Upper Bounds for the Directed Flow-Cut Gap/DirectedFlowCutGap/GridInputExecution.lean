import DirectedFlowCutGap.GridInputBound

namespace DirectedFlowCutGap.GridInputProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem prepare {rows : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 544)) (source : Bits) :
    ∃ ext root,ext.length=cells rows ∧
      NaturalRun program (steps rows+1) (state heap next a b c d stack source 542) []
        (state (heap++ext) (next+ext.length) a b c root stack source 543) ∧
      Prepared (heap++ext) root rows := by
  obtain ⟨ext,root,len,core,rep⟩ := prepare_return input next b c d dense ⟨a,b,c,d⟩ 543 stack source
  have first : tickNatural program (state heap next a b c d stack source 542)=
      some ⟨state heap next a b c d (⟨543,.r3,⟨a,b,c,d⟩⟩::stack) source 500,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩
end DirectedFlowCutGap.GridInputProgram
