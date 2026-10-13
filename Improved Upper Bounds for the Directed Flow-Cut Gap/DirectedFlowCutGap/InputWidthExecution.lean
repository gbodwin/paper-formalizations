import DirectedFlowCutGap.InputWidthBound

namespace DirectedFlowCutGap.InputWidthProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem width (rows : List Fraction) {heap : NaturalHeap} {a : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 208)) (source : Bits) :
    ∃ ext root,ext.length=cells rows ∧
      NaturalRun program (steps rows+1) (state heap next a b c d stack source 206) []
        (state (heap++ext) (next+ext.length) a b c root stack source 207) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.widthList rows).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := width_return rows input next b c d hn ⟨a,b,c,d⟩ 207 stack source
  have first : tickNatural program (state heap next a b c d stack source 206)=
      some ⟨state heap next a b c d (⟨207,.r3,⟨a,b,c,d⟩⟩::stack) source 190,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩
end DirectedFlowCutGap.InputWidthProgram
