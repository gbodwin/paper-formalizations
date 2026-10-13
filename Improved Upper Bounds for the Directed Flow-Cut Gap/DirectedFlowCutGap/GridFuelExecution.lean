import DirectedFlowCutGap.GridFuelBound

namespace DirectedFlowCutGap.GridFuelProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem fuel {dimension width : Bits} {heap : NaturalHeap} {a b : ℕ}
    (dim : BoolList heap a dimension) (wid : BoolList heap b width)
    (next c d : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 256)) (source : Bits) :
    ∃ ext root,ext.length=cells dimension width ∧
      NaturalRun program (steps dimension width+1) (state heap next a b c d stack source 254) []
        (state (heap++ext) (next+ext.length) a b c root stack source 255) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.gridFuel dimension width).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := fuel_return dim wid next c d dense ⟨a,b,c,d⟩ 255 stack source
  have first : tickNatural program (state heap next a b c d stack source 254)=
      some ⟨state heap next a b c d (⟨255,.r3,⟨a,b,c,d⟩⟩::stack) source 200,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩
end DirectedFlowCutGap.GridFuelProgram
