import DirectedFlowCutGap.ShiftedGridCallLift

set_option maxRecDepth 16384

namespace DirectedFlowCutGap.ShiftedGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram CanonicalRationalSum

theorem grid_call {rows : List Fraction} {index exponent : Bits} {heap : NaturalHeap} {a b c : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (exp : BoolList heap c exponent)
    (valid : value index<rows.length) (next d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 1220) (stack : List (Frame ℕ 1220)) (source : Bits) :
    ∃ ext root,ext.length=LambdaGridProgram.cells rows index exponent ∧
      NaturalRun program (LambdaGridProgram.steps rows index exponent+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1038) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (scalar rows index exponent) := by
  obtain ⟨ext,root,len,core,rep⟩ := LambdaGridProgram.compute input idx exp valid next d dense [] source
  have lift := child_return gridLabel LambdaGridProgram.program grid_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [LambdaGridProgram.state,gridLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem row_call {rows : List Fraction} {x : Fraction} {heap : NaturalHeap} {a b : ℕ}
    (table : StoredList heap a rows) (sc : Stored heap b x)
    (next c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 1220) (stack : List (Frame ℕ 1220)) (source : Bits) :
    ∃ ext root,ext.length=ScalarAdditionRow.cells x rows ∧
      NaturalRun program (ScalarAdditionRow.steps x rows+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1198) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (ScalarAdditionRow.result x rows) := by
  obtain ⟨ext,root,len,core,rep⟩ := ScalarAdditionRow.row_high x
    (ScalarAdditionRow.state heap next a b c d [] source 158) rfl dense table sc rfl
  have lift := child_return rowLabel ScalarAdditionRow.program row_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  have count : (1+ScalarAdditionRow.steps x rows)+1=ScalarAdditionRow.steps x rows+2 := by omega
  rw [count] at lift
  exact ⟨ext,root,len,by simpa [ScalarAdditionRow.state,rowLabel,state,Registers.get,Registers.set] using lift,rep⟩
end DirectedFlowCutGap.ShiftedGridProgram
