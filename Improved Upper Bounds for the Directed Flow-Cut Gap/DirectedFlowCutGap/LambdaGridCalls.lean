import DirectedFlowCutGap.LambdaGridCallLift

set_option maxRecDepth 16384

namespace DirectedFlowCutGap.LambdaGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram

theorem grid_call {rows : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 1040) (stack : List (Frame ℕ 1040)) (source : Bits) :
    ∃ ext root,ext.length=GridInputProgram.cells rows ∧
      NaturalRun program (GridInputProgram.steps rows+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 542) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GridInputProgram.Prepared (heap++ext) root rows := by
  obtain ⟨ext,root,len,core,rep⟩ := GridInputProgram.prepare input next b c d dense [] source
  have lift := child_return gridLabel GridInputProgram.program grid_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [GridInputProgram.state,gridLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem row_call {rows : List Fraction} {index dimension exponent : Bits} {heap : NaturalHeap} {a b c d : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (dim : BoolList heap c dimension) (exp : BoolList heap d exponent)
    (valid : value index<rows.length) (next : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 1040) (stack : List (Frame ℕ 1040)) (source : Bits) :
    ∃ ext root,ext.length=LambdaRowProgram.cells rows index dimension exponent ∧
      NaturalRun program (LambdaRowProgram.steps rows index dimension exponent+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1022) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (LambdaRowProgram.result rows index dimension exponent) := by
  obtain ⟨ext,root,len,core,rep⟩ := LambdaRowProgram.compute table idx dim exp valid next dense [] source
  have lift := child_return rowLabel LambdaRowProgram.program row_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [LambdaRowProgram.state,rowLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩
end DirectedFlowCutGap.LambdaGridProgram
