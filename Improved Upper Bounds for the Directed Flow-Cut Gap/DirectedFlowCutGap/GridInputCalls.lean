import DirectedFlowCutGap.GridInputCallLift

namespace DirectedFlowCutGap.GridInputProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem width_call {rows : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 544)
    (stack : List (Frame ℕ 544)) (source : Bits) :
    ∃ ext root,ext.length=InputWidthProgram.cells rows ∧
      NaturalRun program (InputWidthProgram.steps rows+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 206) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (width rows) := by
  obtain ⟨ext,root,len,core,rep⟩ := InputWidthProgram.width rows input next b c d dense [] source
  have lift := child_return widthLabel InputWidthProgram.program width_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [InputWidthProgram.state,widthLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem dimension_call {rows : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 544)
    (stack : List (Frame ℕ 544)) (source : Bits) :
    ∃ ext root,ext.length=1+BinaryLengthProgram.scanCells rows.length [] ∧
      NaturalRun program (BinaryLengthProgram.scanSteps rows.length []+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 224) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (dimension rows) := by
  obtain ⟨out,run,rep,_,_,⟨ext,he,len⟩,nd,st,src,outpc,_⟩ := PackingDimension.count_rows
    (BinaryLengthProgram.state heap next a b c d source 16) rfl dense (PackingSource.capacity input) rfl
  have terminal : program (lengthLabel out.pc)=.ret .r1 := by rw [outpc];rfl
  have lift := child_return lengthLabel BinaryLengthProgram.program length_slots run rfl st .r1 .r3 saved pc stack terminal
  simp only [BinaryLengthProgram.state] at he src
  have nn : out.next=next+ext.length := by rw [nd,he,List.length_append,←dense]
  have hc : 1+BinaryLengthProgram.scanSteps rows.length []+1=BinaryLengthProgram.scanSteps rows.length []+2 := by omega
  rw [hc] at lift
  exact ⟨ext,out.registers.b,len,by simpa [BinaryLengthProgram.state,lengthLabel,state,he,nn,src,
    Registers.set,Registers.get] using lift,by simpa only [he,dimension] using rep⟩

theorem fuel_call {dim wid : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a dim) (right : BoolList heap b wid)
    (next c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 544)
    (stack : List (Frame ℕ 544)) (source : Bits) :
    ∃ ext root,ext.length=GridFuelProgram.cells dim wid ∧
      NaturalRun program (GridFuelProgram.steps dim wid+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 486) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.gridFuel dim wid).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := GridFuelProgram.fuel left right next c d dense [] source
  have lift := child_return fuelLabel GridFuelProgram.program fuel_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [GridFuelProgram.state,fuelLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩
end DirectedFlowCutGap.GridInputProgram
