import DirectedFlowCutGap.EmptyDemandEdgeCallLift

namespace DirectedFlowCutGap.EmptyDemandEdge
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem compare_return {u target : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a u) (right : BoolList heap b target) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 128)
    (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext root, ext.length=BinaryComparisonProgram.cells u target ∧
      NaturalRun program (BinaryComparisonProgram.steps u target+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 84) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u target)) := by
  obtain ⟨ext,root,len,body,tag⟩ := BinaryComparisonProgram.compare_return
    left right next c d hn ⟨a,b,c,d⟩ 47 [] source
  have lift := ReferenceProgramLabels.run cmpLabel BinaryComparisonProgram.program program cmp_slots body
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have core : NaturalRun program (BinaryComparisonProgram.steps u target)
      (state heap next a b c d (⟨47,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 47) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryComparisonProgram.state,cmpLabel,state] using lift
  have first : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 84)=
      some ⟨state heap next a b c d (⟨47,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 0,[],0⟩ := by
    simp [tickNatural,program,state]
  have last : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 47)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using (NaturalRun.step first
        (run_append core (.step last (.done _)))),tag⟩

theorem graph_return {heap : NaturalHeap} {a b : ℕ} {u v : Bits} {rows : List Bits}
    (input : BoolList heap a u) (context : GraphAdjacencyProgram.Context heap b rows v)
    (hi : value u<rows.length) (hj : value v<(rows[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 128)
    (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext root,ext.length=value u+value v+2 ∧ NaturalRun program (GraphAdjacencyProgram.steps u v+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 82) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (rows[value u][value v])) := by
  obtain ⟨ext,root,len,body,rep⟩ := GraphAdjacencyProgram.read_return input context hi hj next c d hn ⟨a,b,c,d⟩ 35 [] source
  have first : tickNatural GraphAdjacencyProgram.program
      (GraphAdjacencyProgram.state heap next a b c d [] source 34)=
      some ⟨GraphAdjacencyProgram.state heap next a b c d [⟨35,.r3,⟨a,b,c,d⟩⟩] source 27,[],0⟩ := by rfl
  have core := NaturalRun.step first body
  have lifted := child_return graphLabel GraphAdjacencyProgram.program graph_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [GraphAdjacencyProgram.state,graphLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
end DirectedFlowCutGap.EmptyDemandEdge
