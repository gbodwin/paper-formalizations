import DirectedFlowCutGap.KeptAdjacencyMatrixCallLift

namespace DirectedFlowCutGap.KeptAdjacencyMatrix
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem row_return {heap : NaturalHeap} {word context : ℕ} {adj kept : Bits} {keep : Bool}
    (hu : BoolList heap word adj) (hc : KeptAdjacencyRow.Context heap context keep kept)
    (aligned : adj.length=kept.length) (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 84)
    (stack : List (Frame ℕ 84)) (source : Bits) :
    ∃ ext root,ext.length=5*adj.length+1 ∧
      NaturalRun program (KeptAdjacencyRow.steps keep adj kept+2)
        (state heap next word context c d (⟨pc,.r3,saved⟩::stack) source 34) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (KeptAdjacencyRow.row keep adj kept) := by
  obtain ⟨ext,root,len,core,rep⟩ := KeptAdjacencyRow.scan hu hc aligned next c d hn [] source
  have lifted := child_return rowLabel KeptAdjacencyRow.program row_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [KeptAdjacencyRow.state,rowLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
end DirectedFlowCutGap.KeptAdjacencyMatrix
