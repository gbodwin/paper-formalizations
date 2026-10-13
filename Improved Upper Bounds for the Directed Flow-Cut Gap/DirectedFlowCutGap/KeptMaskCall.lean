import DirectedFlowCutGap.KeptMaskCallLift

namespace DirectedFlowCutGap.KeptMask
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem keep_return {heap : NaturalHeap} {word context : ℕ} {s t u : Bits} {zero : Bool}
    (hu : BoolList heap word u) (hc : KeptVertex.Context heap context s t zero)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 132)
    (stack : List (Frame ℕ 132)) (source : Bits) :
    ∃ ext root,ext.length=KeptVertex.keepCells s t u zero ∧
      NaturalRun program (KeptVertex.keepSteps s t u zero+2)
        (state heap next word context c d (⟨pc,.r3,saved⟩::stack) source 78) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (KeptVertex.bit s t u zero)) := by
  obtain ⟨ext,root,len,core,rep⟩ := KeptVertex.keep hu hc next c d hn [] source
  have lifted := child_return keepLabel KeptVertex.program keep_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [KeptVertex.state,keepLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
end DirectedFlowCutGap.KeptMask
