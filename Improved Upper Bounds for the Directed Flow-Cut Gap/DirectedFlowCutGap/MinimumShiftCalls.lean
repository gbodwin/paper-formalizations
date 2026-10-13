import DirectedFlowCutGap.MinimumShiftCallLift

set_option maxRecDepth 16384
namespace DirectedFlowCutGap.MinimumShift
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open CanonicalRationalSum

theorem minimum_call {rows : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 1560)
    (stack : List (Frame ℕ 1560)) (source : Bits) :
    ∃ k ext root,k ≤ OriginalRowMinimum.inputSteps rows+1 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 318) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PositiveMinimum.Result (heap++ext) root (OriginalRowMinimum.result rows) := by
  obtain ⟨k,ext,root,bound,run,rep⟩ := OriginalRowMinimum.compute input next b c d dense [] source
  have lift := child_return minimumLabel OriginalRowMinimum.program minimum_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨k+1,ext,root,by omega,by simpa [OriginalRowMinimum.state,minimumLabel,state,Registers.get,Registers.set] using lift,rep⟩

theorem shift_call {rows : List Fraction} {index exponent : Bits} {heap : NaturalHeap} {a b c : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (exp : BoolList heap c exponent)
    (valid : value index<rows.length) (next d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 1560) (stack : List (Frame ℕ 1560)) (source : Bits) :
    ∃ ext root,
      NaturalRun program (ShiftedGridProgram.steps rows index exponent+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1538) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (ShiftedGridProgram.result rows index exponent) := by
  obtain ⟨ext,root,_len,run,rep⟩ := ShiftedGridProgram.compute input idx exp valid next d dense [] source
  have lift := child_return shiftLabel ShiftedGridProgram.program shift_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,by simpa [ShiftedGridProgram.state,shiftLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩
end DirectedFlowCutGap.MinimumShift
