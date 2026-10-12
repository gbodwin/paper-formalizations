import DirectedFlowCutGap.OracleMaskProgram

/-! Reconstructed caller-preserving calls into the real comparison and matrix reader. -/
namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem compare_return {u target : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a u) (right : BoolList heap b target) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 160)
    (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root, ext.length=BinaryComparisonProgram.cells u target ∧
      NaturalRun program (BinaryComparisonProgram.steps u target+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 48) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u target)) := by
  obtain ⟨ext,root,len,body,tag⟩ := BinaryComparisonProgram.compare_return
    left right next c d hn ⟨a,b,c,d⟩ 47 [] source
  have lift := ReferenceProgramLabels.run cmpLabel BinaryComparisonProgram.program program cmp_slots body
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have core : NaturalRun program (BinaryComparisonProgram.steps u target)
      (state heap next a b c d (⟨47,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 47) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryComparisonProgram.state,cmpLabel,state] using lift
  have first : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 48)=
      some ⟨state heap next a b c d (⟨47,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 0,[],0⟩ := by
    simp [tickNatural,program,state]
  have last : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 47)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using (NaturalRun.step first
        (run_append core (.step last (.done _)))),tag⟩

end DirectedFlowCutGap.OracleMask
