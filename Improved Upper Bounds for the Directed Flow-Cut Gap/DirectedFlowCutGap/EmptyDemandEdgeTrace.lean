import DirectedFlowCutGap.EmptyDemandEdgeFinish

namespace DirectedFlowCutGap.EmptyDemandEdge
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def bit (rows : List Bits) (u v : Bits) : Bool :=
  if BinaryComparisonProgram.order u v=.eq then true else GraphRelaxationProgram.adjacent rows u v

def tailSteps (u v : Bits) : ℕ := if BinaryComparisonProgram.order u v=.eq then 3 else GraphAdjacencyProgram.steps u v+7
def tailCells (u v : Bits) : ℕ := if BinaryComparisonProgram.order u v=.eq then 1 else value u+value v+3
def steps (u v : Bits) : ℕ := BinaryComparisonProgram.steps u v+7+tailSteps u v
def cells (u v : Bits) : ℕ := BinaryComparisonProgram.cells u v+1+tailCells u v

theorem finish_return {heap : NaturalHeap} {a b c d original matrixRoot : ℕ} {u v : Bits}
    {rows : List Bits} (htag : heap[d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u v)))
    (hsc : heap[c]?=some (.pair original matrixRoot))
    (hu : BoolList heap a u) (hv : BoolList heap b v) (hm : GraphAdjacencyProgram.Matrix heap matrixRoot rows)
    (hi : value u<rows.length) (hj : value v<(rows[value u]).length)
    (next : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 128)
    (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext out,ext.length=tailCells u v ∧ NaturalRun program (tailSteps u v)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 101) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      (heap++ext)[out]?=some (.flag (bit rows u v)) := by
  cases ho : BinaryComparisonProgram.order u v with
  | eq =>
    refine ⟨[.flag true],next,by simp [tailCells,ho],?_,?_⟩
    · simpa [tailSteps,ho] using equal_return (by simpa [ho,BinaryComparisonProgram.tag] using htag) next saved pc stack source
    · simp [bit,ho,hn]
  | lt =>
    obtain ⟨ext,out,len,run,rep⟩ := different_return (by simpa [ho,BinaryComparisonProgram.tag] using htag)
      hsc hu hv hm hi hj next hn saved pc stack source
    exact ⟨ext,out,by simpa [tailCells,ho] using len,by simpa [tailSteps,ho] using run,
      by simpa [bit,ho,GraphRelaxationProgram.adjacent,hi,hj] using rep⟩
  | gt =>
    obtain ⟨ext,out,len,run,rep⟩ := different_return (by simpa [ho,BinaryComparisonProgram.tag] using htag)
      hsc hu hv hm hi hj next hn saved pc stack source
    exact ⟨ext,out,by simpa [tailCells,ho] using len,by simpa [tailSteps,ho] using run,
      by simpa [bit,ho,GraphRelaxationProgram.adjacent,hi,hj] using rep⟩

theorem edge_return {heap : NaturalHeap} {a b : ℕ} {u v : Bits} {rows : List Bits}
    (hd : Demand heap a u v) (hm : GraphAdjacencyProgram.Matrix heap b rows)
    (hi : value u<rows.length) (hj : value v<(rows[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 128)
    (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext out,ext.length=cells u v ∧ NaturalRun program (steps u v)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 96) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      (heap++ext)[out]?=some (.flag (bit rows u v)) := by
  obtain ⟨ur,vr,ha,hu,hv⟩ := hd
  let scratch : Cell ℕ := .pair a b
  let h0 := heap++[scratch]
  have hsc : h0[next]?=some scratch := by simp [h0,hn]
  have ha0 : h0[a]?=some (.pair ur vr) := lookup_extend ha _
  obtain ⟨e1,tag,l1,cmp,rep⟩ := compare_return (boolList_extend hu [scratch]) (boolList_extend hv [scratch])
    (next+1) next d (by simp [hn]) ⟨ur,vr,next,d⟩ 101 (⟨pc,.r3,saved⟩::stack) source
  let h1 := h0++e1
  let n1 := next+1+e1.length
  obtain ⟨e2,out,l2,finish,outrep⟩ := finish_return rep (lookup_extend hsc e1)
    (boolList_extend (boolList_extend hu _) _) (boolList_extend (boolList_extend hv _) _)
    (GraphAdjacencyProgram.matrix_extend (GraphAdjacencyProgram.matrix_extend hm _) _) hi hj
    n1 (by simp [n1,hn]; omega) saved pc stack source
  refine ⟨[scratch]++e1++e2,out,?_,?_,?_⟩
  · simp [cells,l1,l2];omega
  · have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 96)=
        some ⟨state h0 (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 97,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,scratch]
    have t1 : tickNatural program (state h0 (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 97)=
        some ⟨state h0 (next+1) ur b next d (⟨pc,.r3,saved⟩::stack) source 98,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,ha0]
    have t2 : tickNatural program (state h0 (next+1) ur b next d (⟨pc,.r3,saved⟩::stack) source 98)=
        some ⟨state h0 (next+1) ur a next d (⟨pc,.r3,saved⟩::stack) source 99,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hsc,scratch]
    have t3 : tickNatural program (state h0 (next+1) ur a next d (⟨pc,.r3,saved⟩::stack) source 99)=
        some ⟨state h0 (next+1) ur vr next d (⟨pc,.r3,saved⟩::stack) source 100,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,ha0]
    have t4 : tickNatural program (state h0 (next+1) ur vr next d (⟨pc,.r3,saved⟩::stack) source 100)=
        some ⟨state h0 (next+1) ur vr next d (⟨101,.r3,⟨ur,vr,next,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 84,[],0⟩ := by rfl
    have whole := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (run_append cmp finish)))))
    convert whole using 1 <;> simp [steps,state,n1,List.append_assoc,Nat.add_assoc] <;> omega
  · simpa only [h1,h0,List.append_assoc] using outrep
end DirectedFlowCutGap.EmptyDemandEdge
