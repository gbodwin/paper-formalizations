import DirectedFlowCutGap.GraphRelaxationCalls

/-! Actual input adapters for the scan's adjacency branch, walk extension
and stable original-record comparison. No denotational predicate drives code. -/
namespace DirectedFlowCutGap.GraphRelaxationProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem test_return {heap : NaturalHeap} {a b : ℕ} {x : Entry}
    {adjacency : List Bits} {rows : List Fraction} {u sw : Bits}
    (entry : StoredEntry heap a x) (context : Context heap b adjacency rows u sw)
    (hi : value u<adjacency.length) (hj : value x.1<(adjacency[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 532) (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext root,ext.length=testCells u x.1 ∧ NaturalRun program (testSteps u x.1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 500) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (adjacent adjacency u x.1)) := by
  obtain ⟨vertex,walk,he,hv,_⟩ := entry
  obtain ⟨ur,mix,matrix,cost,hp,hm,hu,ha,_⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair matrix vertex]
  let h0 := heap++e0
  let n0 := next+1
  have dense0 : n0=h0.length := by simp [h0,n0,e0,hn]
  have newctx : GraphAdjacencyProgram.Context h0 next adjacency x.1 :=
    ⟨matrix,vertex,by simp [h0,e0,hn],GraphAdjacencyProgram.matrix_extend ha e0,boolList_extend hv e0⟩
  have oldctx : h0[b]?=some (.pair ur mix) := lookup_extend hp e0
  obtain ⟨ext,root,len,core,flag⟩ := adjacency_return (boolList_extend hu e0) newctx hi hj
    n0 next d dense0 ⟨ur,next,next,d⟩ 507 frames source
  have t500 : tickNatural program (state heap next a b c d frames source 500)=
      some ⟨state heap next vertex b c d frames source 501,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,he]
  have t501 : tickNatural program (state heap next vertex b c d frames source 501)=
      some ⟨state heap next vertex b mix d frames source 502,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have t502 : tickNatural program (state heap next vertex b mix d frames source 502)=
      some ⟨state heap next vertex b matrix d frames source 503,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm]
  have t503 : tickNatural program (state heap next vertex b matrix d frames source 503)=
      some ⟨state h0 n0 vertex b next d frames source 504,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,n0,e0]
  have t504 : tickNatural program (state h0 n0 vertex b next d frames source 504)=
      some ⟨state h0 n0 ur b next d frames source 505,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,oldctx]
  have t505 : tickNatural program (state h0 n0 ur b next d frames source 505)=
      some ⟨state h0 n0 ur next next d frames source 506,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t506 : tickNatural program (state h0 n0 ur next next d frames source 506)=
      some ⟨state h0 n0 ur next next d (⟨507,.r3,⟨ur,next,next,d⟩⟩::frames) source 34,[],0⟩ := by
    simp [tickNatural,program,state]
  have t507 : tickNatural program (state (h0++ext) (n0+ext.length) ur next next root frames source 507)=
      some ⟨state (h0++ext) (n0+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  refine ⟨e0++ext,root,by simp [testCells,e0,len],?_,?_⟩
  · have joined := NaturalRun.step t500 (.step t501 (.step t502 (.step t503 (.step t504
      (.step t505 (.step t506 (run_append core (.step t507 (.done _)))))))))
    convert joined using 1 <;> simp only [testSteps,h0,n0,e0,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,List.append_assoc,Nat.add_assoc,List.nil_append]
  · simpa [h0,List.append_assoc] using flag

theorem extend_return {heap : NaturalHeap} {a b d : ℕ} {e : Bits×Bits} {q : Walk}
    {adjacency : List Bits} {rows : List Fraction} {u sw : Bits}
    (edge : Edge heap a e) (walk : StoredWalk heap d q)
    (context : Context heap b adjacency rows u sw) (hi : value e.1<rows.length)
    (next c : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 532) (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext root,ext.length=GraphWalkExtension.cells rows sw e q ∧
      NaturalRun program (extendSteps rows sw e q)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 510) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredWalk (heap++ext) root (GraphWalkExtension.result rows sw e q) := by
  obtain ⟨ur,mix,matrix,cost,hp,hm,_,_,hc⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨ext,root,len,core,rep⟩ := extension_return edge walk hc hi next d hn
    ⟨a,d,cost,d⟩ 514 frames source
  have t510 : tickNatural program (state heap next a b c d frames source 510)=
      some ⟨state heap next a b mix d frames source 511,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have t511 : tickNatural program (state heap next a b mix d frames source 511)=
      some ⟨state heap next a b cost d frames source 512,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm]
  have t512 : tickNatural program (state heap next a b cost d frames source 512)=
      some ⟨state heap next a d cost d frames source 513,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t513 : tickNatural program (state heap next a d cost d frames source 513)=
      some ⟨state heap next a d cost d (⟨514,.r3,⟨a,d,cost,d⟩⟩::frames) source 304,[],0⟩ := by
    simp [tickNatural,program,state]
  have t514 : tickNatural program (state (heap++ext) (next+ext.length) a d cost root frames source 514)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  refine ⟨ext,root,len,?_,rep⟩
  have joined := NaturalRun.step t510 (.step t511 (.step t512 (.step t513 (run_append core (.step t514 (.done _))))))
  simpa only [extendSteps,Nat.add_assoc,List.nil_append] using joined

theorem choose_return {heap : NaturalHeap} {a b : ℕ} {x y : Walk}
    (left : StoredWalk heap a x) (right : StoredWalk heap b y)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 532) (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext,ext.length=pickCells x y ∧ NaturalRun program (pickSteps x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 520) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c
        (if (BinaryRational.le x.cost y.cost).1 then a else b) stack source pc) ∧
      StoredWalk (heap++ext) (if (BinaryRational.le x.cost y.cost).1 then a else b) (choose x y) := by
  obtain ⟨xe,xc,hx,hxe,hxc⟩ := left
  obtain ⟨ye,yc,hy,hye,hyc⟩ := right
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair a b]
  let h0 := heap++e0
  let n0 := next+1
  have dense0 : n0=h0.length := by simp [h0,n0,e0,hn]
  have xl : h0[a]?=some (.pair xe xc) := lookup_extend hx e0
  have yr : h0[b]?=some (.pair ye yc) := lookup_extend hy e0
  obtain ⟨ext,root,len,core,flag⟩ := rational_return x.cost y.cost
    (RationalComparisonProgram.stored_extend hxc e0) (RationalComparisonProgram.stored_extend hyc e0)
    n0 next d dense0 ⟨xc,yc,next,d⟩ 524 frames source
  let h1 := h0++ext
  let n1 := n0+ext.length
  have flag1 : h1[root]?=some (.flag (BinaryRational.le x.cost y.cost).1) := flag
  have scratch : h1[next]?=some (.pair a b) :=
    lookup_extend (show h0[next]?=some (.pair a b) by simp [h0,e0,hn]) ext
  have t520 : tickNatural program (state heap next a b c d frames source 520)=
      some ⟨state h0 n0 a b next d frames source 521,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,n0,e0]
  have t521 : tickNatural program (state h0 n0 a b next d frames source 521)=
      some ⟨state h0 n0 xc b next d frames source 522,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,xl]
  have t522 : tickNatural program (state h0 n0 xc b next d frames source 522)=
      some ⟨state h0 n0 xc yc next d frames source 523,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,yr]
  have t523 : tickNatural program (state h0 n0 xc yc next d frames source 523)=
      some ⟨state h0 n0 xc yc next d (⟨524,.r3,⟨xc,yc,next,d⟩⟩::frames) source 450,[],0⟩ := by
    simp [tickNatural,program,state]
  have tail : NaturalRun program 3 (state h1 n1 xc yc next root frames source 524) []
      (state h1 n1 saved.a saved.b saved.c
        (if (BinaryRational.le x.cost y.cost).1 then a else b) stack source pc) := by
    cases hk : (BinaryRational.le x.cost y.cost).1 with
    | false =>
      rw [hk] at flag1
      have t524 : tickNatural program (state h1 n1 xc yc next root frames source 524)=
          some ⟨state h1 n1 xc yc next root frames source 526,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,flag1,tagBranch]
      have t526 : tickNatural program (state h1 n1 xc yc next root frames source 526)=
          some ⟨state h1 n1 xc yc next b frames source 527,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
      have t527 : tickNatural program (state h1 n1 xc yc next b frames source 527)=
          some ⟨state h1 n1 saved.a saved.b saved.c b stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      simpa [hk] using NaturalRun.step t524 (.step t526 (.step t527 (.done _)))
    | true =>
      rw [hk] at flag1
      have t524 : tickNatural program (state h1 n1 xc yc next root frames source 524)=
          some ⟨state h1 n1 xc yc next root frames source 525,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,flag1,tagBranch]
      have t525 : tickNatural program (state h1 n1 xc yc next root frames source 525)=
          some ⟨state h1 n1 xc yc next a frames source 527,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
      have t527 : tickNatural program (state h1 n1 xc yc next a frames source 527)=
          some ⟨state h1 n1 saved.a saved.b saved.c a stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      simpa [hk] using NaturalRun.step t524 (.step t525 (.step t527 (.done _)))
  refine ⟨e0++ext,by simp [pickCells,e0,len],?_,?_⟩
  · have joined := NaturalRun.step t520 (.step t521 (.step t522 (.step t523 (run_append core tail))))
    convert joined using 1 <;> simp only [pickSteps,h1,n1,h0,n0,e0,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,List.append_assoc,Nat.add_assoc,List.nil_append]
  · cases hk : (BinaryRational.le x.cost y.cost).1 with
    | false => simpa only [choose,hk,Bool.false_eq_true,ite_false,ite_true,List.append_assoc] using walk_extend (walk_extend ⟨ye,yc,hy,hye,hyc⟩ e0) ext
    | true => simpa only [choose,hk,Bool.false_eq_true,ite_false,ite_true,List.append_assoc] using walk_extend (walk_extend ⟨xe,xc,hx,hxe,hxc⟩ e0) ext

end DirectedFlowCutGap.GraphRelaxationProgram
