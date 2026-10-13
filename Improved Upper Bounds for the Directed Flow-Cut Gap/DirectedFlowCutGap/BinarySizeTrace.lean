import DirectedFlowCutGap.BinarySizeCalls

namespace DirectedFlowCutGap.BinarySizeProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem size_return {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 48) (stack : List (Frame ℕ 48)) (source : Bits) :
    ∃ ext root,ext.length=cells word ∧
      NaturalRun program (steps word)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 38) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryCounters.sizeBits word).1 := by
  let frame : Frame ℕ 48 := ⟨pc,.r3,saved⟩
  obtain ⟨ext,trimmed,len,first,rep⟩ := trim_call input next b c d hn
    ⟨a,b,c,d⟩ 39 (frame::stack) source
  obtain ⟨more,root,mlen,second,answer⟩ := length_call rep (next+ext.length) b c trimmed
    (by simp [hn]) ⟨trimmed,b,c,trimmed⟩ 41 (frame::stack) source
  have t38 : tickNatural program (state heap next a b c d (frame::stack) source 38)=
      some ⟨state heap next a b c d (⟨39,.r3,⟨a,b,c,d⟩⟩::frame::stack) source 11,[],0⟩ := by rfl
  have t39 : tickNatural program (state (heap++ext) (next+ext.length) a b c trimmed (frame::stack) source 39)=
      some ⟨state (heap++ext) (next+ext.length) trimmed b c trimmed (frame::stack) source 40,[],0⟩ := by rfl
  have t40 : tickNatural program (state (heap++ext) (next+ext.length) trimmed b c trimmed (frame::stack) source 40)=
      some ⟨state (heap++ext) (next+ext.length) trimmed b c trimmed
        (⟨41,.r3,⟨trimmed,b,c,trimmed⟩⟩::frame::stack) source 29,[],0⟩ := by rfl
  have t41 : tickNatural program
      (state ((heap++ext)++more) (next+ext.length+more.length) trimmed b c root (frame::stack) source 41)=
      some ⟨state ((heap++ext)++more) (next+ext.length+more.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  refine ⟨ext++more,root,by simp [cells,len,mlen,Nat.add_assoc],?_,?_⟩
  · have all := NaturalRun.step t38 (run_append first (.step t39 (.step t40
      (run_append second (.step t41 (.done _))))))
    convert all using 1 <;> simp [steps,state,List.append_assoc,Nat.add_assoc]
    omega
  · simpa only [BinaryCounters.sizeBits,List.append_assoc] using answer
end DirectedFlowCutGap.BinarySizeProgram
