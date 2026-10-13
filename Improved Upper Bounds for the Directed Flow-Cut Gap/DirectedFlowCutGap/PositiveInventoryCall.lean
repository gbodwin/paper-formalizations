import DirectedFlowCutGap.PositiveInventoryCallLift

namespace DirectedFlowCutGap.PositiveInventory
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem zero_return {heap : NaturalHeap} {a : ℕ} {word : Bits}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (destination : Reg) (pc : Fin 48)
    (stack : List (Frame ℕ 48)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+2)
      (state heap next a b c d (⟨pc,destination,saved⟩::stack) source 7) []
      ⟨heap++[.flag (isZero word).1],next+1,saved.set destination next,stack,pc,source⟩ := by
  have body := BinaryZeroProgram.zero_return input next b c d hn ⟨a,b,c,d⟩ 8 [] source
  have call : tickNatural BinaryZeroProgram.program
      (BinaryZeroProgram.state heap next a b c d [] source 7)=some
      ⟨BinaryZeroProgram.state heap next a b c d [⟨8,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by rfl
  have core := NaturalRun.step call body
  have lifted := child_return zeroLabel BinaryZeroProgram.program zero_slots core rfl rfl
    .r3 destination saved pc stack (by rfl)
  simpa [BinaryZeroProgram.state,zeroLabel,state,Registers.get,Nat.add_assoc] using lifted
end DirectedFlowCutGap.PositiveInventory
