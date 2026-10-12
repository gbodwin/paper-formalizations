import DirectedFlowCutGap.PackingGuardProgram

namespace DirectedFlowCutGap.PackingGuard
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem comparison_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 484) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ ext root,ext.length=RationalComparisonProgram.cells x y ∧
      NaturalRun program (RationalComparisonProgram.instructions x y+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 456) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (BinaryRational.le x y).1) := by
  obtain ⟨out,high,flag,_,_,src,frames,hpc,dense,⟨ext,he,len⟩,_⟩ :=
    RationalComparisonProgram.run_high x y
      (RationalComparisonProgram.state heap next a b c d [] source 144) rfl hn left right rfl
  have shape : out=⟨heap++ext,next+ext.length,out.registers,[],157,source⟩ := by
    cases out
    simp_all [RationalComparisonProgram.state]
  rw [shape] at high flag
  have run := call_run comparisonLabel RationalComparisonProgram.program comparison_slots high
    (by simp [program,comparisonLabel,RationalComparisonProgram.program,callable]) saved pc stack
  refine ⟨ext,out.registers.d,len,?_,flag⟩
  simpa [state,RationalComparisonProgram.state,comparisonLabel] using run
end DirectedFlowCutGap.PackingGuard
