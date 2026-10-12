import DirectedFlowCutGap.GraphDiscoveryCalls

/-! The real target test either allocates the literal empty zero walk or calls
the actual scan with a newly constructed one-vertex context on the same heap. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem unequal_return {heap : NaturalHeap} {a b p : ℕ} {u target sw : Bits}
    {adjacency : List Bits} {rows : List Fraction} {old : List Entry}
    (input : BoolList heap a u) (context : Context heap b adjacency rows sw target old)
    (scratch : heap[p]?=some (.pair a b))
    (hi : value u<adjacency.length) (hc : value u<rows.length)
    (hcols : ∀ x∈old,value x.1<(adjacency[value u]).length)
    (next t d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=1+GraphRelaxationProgram.cells adjacency rows sw u old ∧
      NaturalRun program (GraphRelaxationProgram.steps adjacency rows sw u old+11)
        (state heap next a t p d (⟨pc,.r3,saved⟩::stack) source 604) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (GraphRelaxationProgram.scan adjacency rows sw u old) := by
  obtain ⟨tr,bundle,oldRoot,mix,matrix,cost,hp,hb,hm,_,ho,ha,hcost⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair a mix]
  let h0 := heap++e0
  let n0 := next+1
  have dense : n0=h0.length := by simp [n0,h0,e0,hn]
  have newctx : GraphRelaxationProgram.Context h0 next adjacency rows u sw :=
    ⟨a,mix,matrix,cost,by simp [h0,e0,hn],lookup_extend hm e0,boolList_extend input e0,
      GraphAdjacencyProgram.matrix_extend ha e0,PathCostMaterialization.context_extend hcost e0⟩
  obtain ⟨ext,root,len,body,rep⟩ := scan_return (GraphRelaxationProgram.table_extend ho e0)
    newctx hi hc hcols n0 p next dense ⟨oldRoot,next,p,next⟩ 612 frames source
  have t604 : tickNatural program (state heap next a t p d frames source 604)=
      some ⟨state heap next a t p d frames source 605,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t605 : tickNatural program (state heap next a t p d frames source 605)=
      some ⟨state heap next a b p d frames source 606,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t606 : tickNatural program (state heap next a b p d frames source 606)=
      some ⟨state heap next a bundle p d frames source 607,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have t607 : tickNatural program (state heap next a bundle p d frames source 607)=
      some ⟨state heap next a bundle p mix frames source 608,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  have t608 : tickNatural program (state heap next a bundle p mix frames source 608)=
      some ⟨state h0 n0 a bundle p next frames source 609,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,n0,e0]
  have t609 : tickNatural program (state h0 n0 a bundle p next frames source 609)=
      some ⟨state h0 n0 oldRoot bundle p next frames source 610,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h0,lookup_extend hb e0]
  have t610 : tickNatural program (state h0 n0 oldRoot bundle p next frames source 610)=
      some ⟨state h0 n0 oldRoot next p next frames source 611,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t611 : tickNatural program (state h0 n0 oldRoot next p next frames source 611)=
      some ⟨state h0 n0 oldRoot next p next (⟨612,.r3,⟨oldRoot,next,p,next⟩⟩::frames) source 530,[],0⟩ := by
    simp [tickNatural,program,state]
  have t612 : tickNatural program (state (h0++ext) (n0+ext.length) oldRoot next p root frames source 612)=
      some ⟨state (h0++ext) (n0+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  have joined := NaturalRun.step t604 (.step t605 (.step t606 (.step t607 (.step t608
    (.step t609 (.step t610 (.step t611 (run_append body (.step t612 (.done _))))))))))
  refine ⟨e0++ext,root,by simp only [e0,List.length_append,List.length_cons,List.length_nil,len],?_,?_⟩
  · convert joined using 1 <;> simp only [h0,n0,e0,List.append_assoc,List.length_append,List.length_cons,List.length_nil,Nat.add_assoc,Nat.zero_add,List.nil_append]
  · simpa [h0,List.append_assoc] using rep


def vertexTailSteps (adjacency : List Bits) (rows : List Fraction) (sw target u : Bits)
    (old : List Entry) : ℕ :=
  if BinaryComparisonProgram.order u target=.eq then 7 else
    GraphRelaxationProgram.steps adjacency rows sw u old+12

def vertexTailCells (adjacency : List Bits) (rows : List Fraction) (sw target u : Bits)
    (old : List Entry) : ℕ :=
  if BinaryComparisonProgram.order u target=.eq then 5 else
    1+GraphRelaxationProgram.cells adjacency rows sw u old

theorem vertex_tail {heap : NaturalHeap} {a b p d : ℕ} {u target sw : Bits}
    {adjacency : List Bits} {rows : List Fraction} {old : List Entry}
    (input : BoolList heap a u) (context : Context heap b adjacency rows sw target old)
    (scratch : heap[p]?=some (.pair a b))
    (tag : heap[d]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u target)))
    (hi : value u<adjacency.length) (hc : value u<rows.length)
    (hcols : ∀ x∈old,value x.1<(adjacency[value u]).length)
    (next t : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=vertexTailCells adjacency rows sw target u old ∧
      NaturalRun program (vertexTailSteps adjacency rows sw target u old)
        (state heap next a t p d (⟨pc,.r3,saved⟩::stack) source 603) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (atVertex adjacency rows sw target u old) := by
  have branch : tickNatural program (state heap next a t p d (⟨pc,.r3,saved⟩::stack) source 603)=
      some ⟨state heap next a t p d (⟨pc,.r3,saved⟩::stack) source
        (if BinaryComparisonProgram.order u target=.eq then 590 else 604),[],0⟩ := by
    cases ho : BinaryComparisonProgram.order u target <;>
      simp [tickNatural,program,state,Registers.get,tag,ho,BinaryComparisonProgram.tag,tagBranch]
  by_cases he : BinaryComparisonProgram.order u target=.eq
  · obtain ⟨ext,root,len,body,rep⟩ := zero_return heap next a t p d hn saved pc stack source
    simp only [he,ite_true] at branch
    exact ⟨ext,root,by simpa [vertexTailCells,he] using len,
      by simpa [vertexTailSteps,he] using NaturalRun.step branch body,
      by simpa [atVertex,he,StoredOption,GraphRelaxationProgram.StoredOption] using rep⟩
  · obtain ⟨ext,root,len,body,rep⟩ := unequal_return input context scratch hi hc hcols next t d hn saved pc stack source
    simp only [he,ite_false] at branch
    exact ⟨ext,root,by simpa [vertexTailCells,he] using len,
      by simpa [vertexTailSteps,he,Nat.add_assoc] using NaturalRun.step branch body,
      by simpa [atVertex,he] using rep⟩

/-- The exact target branch is selected by a real padded-word comparison,
then calls actual zero allocation or actual graph relaxation. -/
theorem vertex_return {heap : NaturalHeap} {a b : ℕ} {u target sw : Bits}
    {adjacency : List Bits} {rows : List Fraction} {old : List Entry}
    (input : BoolList heap a u) (context : Context heap b adjacency rows sw target old)
    (hi : value u<adjacency.length) (hc : value u<rows.length)
    (hcols : ∀ x∈old,value x.1<(adjacency[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=atCells adjacency rows sw target u old ∧
      NaturalRun program (atSteps adjacency rows sw target u old)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 600) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (atVertex adjacency rows sw target u old) := by
  obtain ⟨tr,bundle,oldRoot,mix,matrix,cost,hp,hb,hm,ht,ho,ha,hcost⟩ := context
  have context : Context heap b adjacency rows sw target old :=
    ⟨tr,bundle,oldRoot,mix,matrix,cost,hp,hb,hm,ht,ho,ha,hcost⟩
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair a b]
  let h0 := heap++e0
  let n0 := next+1
  have dense0 : n0=h0.length := by simp [h0,n0,e0,hn]
  have scratch : h0[next]?=some (.pair a b) := by simp [h0,e0,hn]
  obtain ⟨ec,rc,lc,runC,tag⟩ := compare_return (boolList_extend input e0) (boolList_extend ht e0)
    n0 next d dense0 ⟨a,tr,next,d⟩ 603 frames source
  let h1 := h0++ec
  let n1 := n0+ec.length
  have dense1 : n1=h1.length := by simp [h1,n1,dense0]
  obtain ⟨ef,rf,lf,runF,repF⟩ := vertex_tail (boolList_extend (boolList_extend input e0) ec)
    (context_extend (context_extend context e0) ec) (lookup_extend scratch ec) tag
    hi hc hcols n1 tr dense1 saved pc stack source
  have t600 : tickNatural program (state heap next a b c d frames source 600)=
      some ⟨state h0 n0 a b next d frames source 601,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,n0,e0]
  have t601 : tickNatural program (state h0 n0 a b next d frames source 601)=
      some ⟨state h0 n0 a tr next d frames source 602,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h0,lookup_extend hp e0]
  have t602 : tickNatural program (state h0 n0 a tr next d frames source 602)=
      some ⟨state h0 n0 a tr next d (⟨603,.r3,⟨a,tr,next,d⟩⟩::frames) source 580,[],0⟩ := by
    simp [tickNatural,program,state]
  let ext := e0++ec++ef
  have shape : heap++ext=h1++ef := by simp [ext,h1,h0,List.append_assoc]
  have count : next+ext.length=n1+ef.length := by simp only [ext,n1,n0,e0,List.length_append,List.length_cons,List.length_nil];omega
  refine ⟨ext,rf,?_,?_,?_⟩
  · simp only [ext,List.length_append,lc,lf,e0,List.length_cons,List.length_nil]
    simp [atCells,vertexTailCells,Nat.add_assoc]
  · have joined := NaturalRun.step t600 (.step t601 (.step t602 (run_append runC runF)))
    rw [shape,count]
    convert joined using 1 <;> try rfl
    simp only [atSteps,vertexTailSteps]
    split_ifs <;> omega
  · rw [shape];exact repF

end DirectedFlowCutGap.GraphDiscoveryProgram
