import DirectedFlowCutGap.PackingIterationCallLift

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

set_option maxRecDepth 10000 in
theorem counter_return {heap : NaturalHeap} {a : ℕ} {fuel : Bits}
    (table : BoolList heap a fuel) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4860) (stack : List (Frame ℕ 4860)) (source : Bits) :
    ∃ ext root, ext.length=BinaryCounterProgram.cells fuel ∧
      NaturalRun program (BinaryCounterProgram.steps fuel+2)
        (state heap next a b c d (⟨pc,.r2,saved⟩::stack) source 4817) []
        (state (heap++ext) (next+ext.length) saved.a saved.b root saved.d stack source pc) ∧
      IndexSpine (heap++ext) root (value fuel) := by
  obtain ⟨ext,root,len,run,rep⟩ := BinaryCounterProgram.convert_return table next b c d dense
    ⟨a,b,c,d⟩ 16 [] source
  have lifted := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program counter_slots run
  have body := ReferenceProgramStack.run program (⟨pc,.r2,saved⟩::stack) lifted
  have body' : NaturalRun program (BinaryCounterProgram.steps fuel)
      (state heap next a b c d (⟨4816,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r2,saved⟩::stack) source 4800) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r2,saved⟩::stack) source 4816) := by
    simpa [ReferenceProgramStack.state,ReferenceProgramLabels.state,ReferenceProgramLabels.frame,
      BinaryCounterProgram.state,counterLabel,state,len] using body
  have call : tickNatural program (state heap next a b c d (⟨pc,.r2,saved⟩::stack) source 4817)=
      some ⟨state heap next a b c d (⟨4816,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r2,saved⟩::stack) source 4800,[],0⟩ := by
    have slot : program 4817=.call 4800 4816 .r3 := rfl
    simp [tickNatural,state,slot]
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r2,saved⟩::stack) source 4816)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b root saved.d stack source pc,[],0⟩ := by
    have slot : program 4816=.ret .r3 := by norm_num [program,callable,BinaryCounterProgram.program]
    simp [tickNatural,state,slot,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  simpa only [Nat.add_assoc,List.append_nil] using NaturalRun.step call (run_append body' (.step ret (.done _)))
end DirectedFlowCutGap.PackingIteration
