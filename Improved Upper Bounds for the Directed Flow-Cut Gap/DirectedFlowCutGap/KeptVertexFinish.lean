import DirectedFlowCutGap.KeptVertexComparison

namespace DirectedFlowCutGap.KeptVertex
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem flag_return (bit : Bool) (heap : NaturalHeap) (next a b c d : ℕ)
    (saved : Registers ℕ) (pc : Fin 80) (stack : List (Frame ℕ 80)) (source : Bits) :
    NaturalRun program 2
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (if bit then 70 else 72)) []
      (state (heap++[.flag bit]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have first : tickNatural program
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (if bit then 70 else 72))=
      some ⟨state (heap++[.flag bit]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack)
        source (if bit then 71 else 73),[],0⟩ := by
    cases bit <;> simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
  have last : tickNatural program
      (state (heap++[.flag bit]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack)
        source (if bit then 71 else 73))=
      some ⟨state (heap++[.flag bit]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    cases bit <;> simp [tickNatural,program,state,Registers.get,Registers.set]
  exact .step first (.step last (.done _))

theorem finish_return {heap : NaturalHeap} {u v : Bits} {d : ℕ}
    (tag : heap[d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u v)))
    (next a b c : ℕ) (saved : Registers ℕ) (pc : Fin 80)
    (stack : List (Frame ℕ 80)) (source : Bits) :
    NaturalRun program 3
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 61) []
      (state (heap++[.flag (same u v)]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have branch : tickNatural program
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 61)=
      some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack)
        source (if same u v then 70 else 72),[],0⟩ := by
    cases ho : BinaryComparisonProgram.order u v <;>
      simp [tickNatural,program,state,Registers.get,tag,ho,BinaryComparisonProgram.tag,tagBranch,same,SupportRecoveryProgram.same]
  exact .step branch (flag_return (same u v) heap next a b c d saved pc stack source)

end DirectedFlowCutGap.KeptVertex
