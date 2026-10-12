import DirectedFlowCutGap.PackingUpdateRowProgram

namespace DirectedFlowCutGap.PackingUpdateRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem entry_return (ci amount y : Fraction) {heap : NaturalHeap} {a b c : ℕ}
    (cap : Stored heap a ci) (amt : Stored heap b amount) (weight : Stored heap c y)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 520) (stack : List (Frame ℕ 520)) (source : Bits) :
    ∃ ext root,ext.length=PackingEntry.cells ci amount y ∧
      NaturalRun program (PackingEntry.steps ci amount y+1)
        (state heap next a b c d (⟨pc,.r0,saved⟩::stack) source 440) []
        (state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc) ∧
      Stored (heap++ext) root (PackingEntry.result ci amount y) := by
  obtain ⟨ext,factorRoot,root,len,high,rep⟩ := PackingEntry.entry_high ci amount y cap amt weight next d hn source
  have lifted := ReferenceProgramLabels.run label PackingEntry.program program slots high
  have lifted := ReferenceProgramStack.run program (⟨pc,.r0,saved⟩::stack) lifted
  have body : NaturalRun program (PackingEntry.steps ci amount y)
      (state heap next a b c d (⟨pc,.r0,saved⟩::stack) source 440) []
      (state (heap++ext) (next+ext.length) c factorRoot (next+9) root (⟨pc,.r0,saved⟩::stack) source 467) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramStack.state,label,state,PackingEntry.state] using lifted
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) c factorRoot (next+9) root (⟨pc,.r0,saved⟩::stack) source 467)=
      some ⟨state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,callable,PackingEntry.program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa using run_append body (.step ret (.done _)),rep⟩
end DirectedFlowCutGap.PackingUpdateRow
