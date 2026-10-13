import DirectedFlowCutGap.PackingParametersCallLift

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation PackedBooleanConstructor
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList)

theorem dimension_return {row : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : StoredList heap a row) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 360) (stack : List (Frame ℕ 360)) (source : Bits) :
    ∃ ext root, ext.length=1+BinaryLengthProgram.scanCells row.length [] ∧
      NaturalRun program (BinaryLengthProgram.scanSteps row.length []+2)
        (state heap next a b c d (⟨pc,.r0,saved⟩::stack) source 16) []
        (state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc) ∧
      BoolList (heap++ext) root (BinaryLengthProgram.countWord row.length []) := by
  obtain ⟨out,run,rep,_,_,⟨ext,he,len⟩,nd,st,src,outpc,_⟩ := PackingDimension.count_rows
    (BinaryLengthProgram.state heap next a b c d source 16) rfl dense input rfl
  have terminal : BinaryLengthProgram.program out.pc=.halt := by rw [outpc];rfl
  have lifted := child_return lengthLabel BinaryLengthProgram.program length_slots run rfl st .r1 .r0 saved pc stack
    (length_halt out.pc terminal)
  simp only [BinaryLengthProgram.state] at he src
  have nn : out.next=next+ext.length := by rw [nd,he,List.length_append,←dense]
  have entry : lengthLabel 16=(16 : Fin 360) := by decide
  have hc : 1+BinaryLengthProgram.scanSteps row.length []+1=BinaryLengthProgram.scanSteps row.length []+2 := by omega
  rw [hc] at lifted
  exact ⟨ext,out.registers.b,len,by simpa only [BinaryLengthProgram.state,entry,state,he,nn,src,
    Registers.set,Registers.get] using lifted,by simpa only [he] using rep⟩
end DirectedFlowCutGap.PackingParameters
