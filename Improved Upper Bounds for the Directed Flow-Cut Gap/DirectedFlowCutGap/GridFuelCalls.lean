import DirectedFlowCutGap.GridFuelCallLift

namespace DirectedFlowCutGap.GridFuelProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem size_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 256) (stack : List (Frame ℕ 256)) (source : Bits) :
    ∃ ext root,ext.length=BinarySizeProgram.cells word ∧
      NaturalRun program (BinarySizeProgram.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 162) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryCounters.sizeBits word).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := BinarySizeProgram.size input next b c d hn [] source
  have lift := child_return sizeLabel BinarySizeProgram.program size_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [BinarySizeProgram.state,sizeLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem arithmetic_call (product : Bool) {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 256)
    (stack : List (Frame ℕ 256)) (source : Bits) :
    ∃ ext root,ext.length=arithmeticCells product xs ys ∧
      NaturalRun program (CanonicalArithmeticProgram.instructions product xs ys+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source
          (arithmeticLabel (CanonicalArithmeticProgram.top product))) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (if product then mulCanonical xs ys else addCanonical xs ys).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalArithmeticProgram.canonical_high product
    (CanonicalArithmeticProgram.state heap next a b c d [] source (CanonicalArithmeticProgram.top product)) rfl hn left right rfl
  have lift := child_return arithmeticLabel CanonicalArithmeticProgram.program arithmetic_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [CanonicalArithmeticProgram.state,arithmeticLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,by simpa only [CanonicalArithmeticProgram.result_exact,CanonicalArithmeticProgram.state] using rep⟩
end DirectedFlowCutGap.GridFuelProgram
