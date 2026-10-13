import DirectedFlowCutGap.EmptyDemandScanCallLift

namespace DirectedFlowCutGap.EmptyDemandScan
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem edge_return {heap : NaturalHeap} {a b : ℕ} {u v : Bits} {rows : List Bits}
    (hd : EmptyDemandEdge.Demand heap a u v) (hm : GraphAdjacencyProgram.Matrix heap b rows)
    (hi : value u<rows.length) (hj : value v<(rows[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 160)
    (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root,ext.length=EmptyDemandEdge.cells u v ∧ NaturalRun program (EmptyDemandEdge.steps u v+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 126) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (EmptyDemandEdge.bit rows u v)) := by
  obtain ⟨ext,root,len,core,rep⟩ := EmptyDemandEdge.scan hd hm hi hj next c d hn [] source
  have lifted := child_return edgeLabel EmptyDemandEdge.program edge_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [EmptyDemandEdge.state,edgeLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
end DirectedFlowCutGap.EmptyDemandScan
