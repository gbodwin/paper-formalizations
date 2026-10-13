import DirectedFlowCutGap.EmptyDemandEdgeCalls

namespace DirectedFlowCutGap.EmptyDemandEdge
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem equal_return {heap : NaturalHeap} {tag a b c : ℕ} (ht : heap[tag]?=some .nil)
    (next : ℕ) (saved : Registers ℕ) (pc : Fin 128)
    (stack : List (Frame ℕ 128)) (source : Bits) :
    NaturalRun program 3 (state heap next a b c tag (⟨pc,.r3,saved⟩::stack) source 101) []
      (state (heap++[.flag true]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have t0 : tickNatural program (state heap next a b c tag (⟨pc,.r3,saved⟩::stack) source 101)=
      some ⟨state heap next a b c tag (⟨pc,.r3,saved⟩::stack) source 118,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,tagBranch,ht]
  have t1 : tickNatural program (state heap next a b c tag (⟨pc,.r3,saved⟩::stack) source 118)=
      some ⟨state (heap++[.flag true]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 119,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
  have t2 : tickNatural program (state (heap++[.flag true]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 119)=
      some ⟨state (heap++[.flag true]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact .step t0 (.step t1 (.step t2 (.done _)))

theorem different_return {heap : NaturalHeap} {a b c d original matrixRoot : ℕ} {u v : Bits}
    {rows : List Bits} {flag : Bool} (htag : heap[d]?=some (.flag flag))
    (hsc : heap[c]?=some (.pair original matrixRoot))
    (hu : BoolList heap a u) (hv : BoolList heap b v) (hm : GraphAdjacencyProgram.Matrix heap matrixRoot rows)
    (hi : value u<rows.length) (hj : value v<(rows[value u]).length)
    (next : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 128)
    (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext out,ext.length=value u+value v+3 ∧ NaturalRun program (GraphAdjacencyProgram.steps u v+7)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 101) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      (heap++ext)[out]?=some (.flag (rows[value u][value v])) := by
  let ctx : Cell ℕ := .pair matrixRoot b
  let h0 := heap++[ctx]
  have hctx : GraphAdjacencyProgram.Context h0 next rows v :=
    ⟨matrixRoot,b,by simp [h0,hn,ctx],GraphAdjacencyProgram.matrix_extend hm _,boolList_extend hv _⟩
  obtain ⟨ext,out,len,run,rep⟩ := graph_return (boolList_extend hu [ctx]) hctx hi hj
    (next+1) c matrixRoot (by simp [hn]) ⟨a,next,c,matrixRoot⟩ 105 (⟨pc,.r3,saved⟩::stack) source
  refine ⟨[ctx]++ext,out,by simp only [List.length_append,List.length_singleton];omega,?_,?_⟩
  · have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 101)=
        some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 102,[],0⟩ := by
      cases flag <;> simp [tickNatural,program,state,Registers.get,tagBranch,htag]
    have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 102)=
        some ⟨state heap next a b c matrixRoot (⟨pc,.r3,saved⟩::stack) source 103,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hsc]
    have t2 : tickNatural program (state heap next a b c matrixRoot (⟨pc,.r3,saved⟩::stack) source 103)=
        some ⟨state h0 (next+1) a next c matrixRoot (⟨pc,.r3,saved⟩::stack) source 104,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,ctx]
    have t3 : tickNatural program (state h0 (next+1) a next c matrixRoot (⟨pc,.r3,saved⟩::stack) source 104)=
        some ⟨state h0 (next+1) a next c matrixRoot (⟨105,.r3,⟨a,next,c,matrixRoot⟩⟩::⟨pc,.r3,saved⟩::stack) source 82,[],0⟩ := by rfl
    have t4 : tickNatural program (state (h0++ext) (next+1+ext.length) a next c out (⟨pc,.r3,saved⟩::stack) source 105)=
        some ⟨state (h0++ext) (next+1+ext.length) saved.a saved.b saved.c out stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have whole := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (run_append run (.step t4 (.done _))))))
    convert whole using 1 <;> simp [state,h0,List.append_assoc,Nat.add_assoc]; omega
  · simpa only [h0,List.append_assoc] using rep
end DirectedFlowCutGap.EmptyDemandEdge
