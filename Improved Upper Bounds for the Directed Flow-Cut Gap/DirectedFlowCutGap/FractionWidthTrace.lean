import DirectedFlowCutGap.FractionWidthCalls

namespace DirectedFlowCutGap.FractionWidthProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem width_return {q : BinaryRational.Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : RationalComparisonProgram.Stored heap a q) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 128) (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext root,ext.length=cells q ∧
      NaturalRun program (steps q)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 110) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.fractionWidth q).1 := by
  obtain ⟨num,den,pair,nrep,drep⟩ := input
  let frame : Frame ℕ 128 := ⟨pc,.r3,saved⟩
  obtain ⟨en,nroot,nlen,nrun,ns⟩ := size_call nrep next b a d hn ⟨num,b,a,d⟩ 113 (frame::stack) source
  obtain ⟨ed,droot,dlen,drun,ds⟩ := size_call (boolList_extend drep en) (next+en.length) nroot a nroot
    (by simp [hn]) ⟨den,nroot,a,nroot⟩ 116 (frame::stack) source
  obtain ⟨em,root,mlen,mrun,answer⟩ := max_call (boolList_extend ns ed) ds
    (next+en.length+ed.length) a droot (by simp [hn,Nat.add_assoc])
    ⟨nroot,droot,a,droot⟩ 119 (frame::stack) source
  have t110 : tickNatural program (state heap next a b c d (frame::stack) source 110)=
      some ⟨state heap next a b a d (frame::stack) source 111,[],0⟩ := by rfl
  have t111 : tickNatural program (state heap next a b a d (frame::stack) source 111)=
      some ⟨state heap next num b a d (frame::stack) source 112,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair]
  have t112 : tickNatural program (state heap next num b a d (frame::stack) source 112)=
      some ⟨state heap next num b a d (⟨113,.r3,⟨num,b,a,d⟩⟩::frame::stack) source 46,[],0⟩ := by rfl
  have t113 : tickNatural program (state (heap++en) (next+en.length) num b a nroot (frame::stack) source 113)=
      some ⟨state (heap++en) (next+en.length) num nroot a nroot (frame::stack) source 114,[],0⟩ := by rfl
  have t114 : tickNatural program (state (heap++en) (next+en.length) num nroot a nroot (frame::stack) source 114)=
      some ⟨state (heap++en) (next+en.length) den nroot a nroot (frame::stack) source 115,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend pair en]
  have t115 : tickNatural program (state (heap++en) (next+en.length) den nroot a nroot (frame::stack) source 115)=
      some ⟨state (heap++en) (next+en.length) den nroot a nroot
        (⟨116,.r3,⟨den,nroot,a,nroot⟩⟩::frame::stack) source 46,[],0⟩ := by rfl
  have t116 : tickNatural program
      (state ((heap++en)++ed) (next+en.length+ed.length) den nroot a droot (frame::stack) source 116)=
      some ⟨state ((heap++en)++ed) (next+en.length+ed.length) nroot nroot a droot (frame::stack) source 117,[],0⟩ := by rfl
  have t117 : tickNatural program
      (state ((heap++en)++ed) (next+en.length+ed.length) nroot nroot a droot (frame::stack) source 117)=
      some ⟨state ((heap++en)++ed) (next+en.length+ed.length) nroot droot a droot (frame::stack) source 118,[],0⟩ := by rfl
  have t118 : tickNatural program
      (state ((heap++en)++ed) (next+en.length+ed.length) nroot droot a droot (frame::stack) source 118)=
      some ⟨state ((heap++en)++ed) (next+en.length+ed.length) nroot droot a droot
        (⟨119,.r3,⟨nroot,droot,a,droot⟩⟩::frame::stack) source 102,[],0⟩ := by rfl
  have t119 : tickNatural program
      (state (((heap++en)++ed)++em) (next+en.length+ed.length+em.length) nroot droot a root (frame::stack) source 119)=
      some ⟨state (((heap++en)++ed)++em) (next+en.length+ed.length+em.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  refine ⟨en++ed++em,root,by simp [cells,nlen,dlen,mlen,Nat.add_assoc],?_,?_⟩
  · have all := NaturalRun.step t110 (.step t111 (.step t112 (run_append nrun
      (.step t113 (.step t114 (.step t115 (run_append drun
        (.step t116 (.step t117 (.step t118 (run_append mrun (.step t119 (.done _)))))))))))))
    convert all using 1 <;> simp [steps,state,List.append_assoc,Nat.add_assoc]
    omega
  · simpa only [BinaryFractionalGuesses.fractionWidth,List.append_assoc] using answer
end DirectedFlowCutGap.FractionWidthProgram
