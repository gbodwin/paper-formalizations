import DirectedFlowCutGap.GraphRelaxationProgram

/-! The graph scan's three real subroutine calls, with their actual saved
registers, shared heap and instruction counts. -/
namespace DirectedFlowCutGap.GraphRelaxationProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem adjacency_return {heap : NaturalHeap} {a b : ℕ} {u v : Bits} {rows : List Bits}
    (input : BoolList heap a u) (context : GraphAdjacencyProgram.Context heap b rows v)
    (hi : value u<rows.length) (hj : value v<(rows[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 532) (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext root,ext.length=value u+value v+2 ∧
      NaturalRun program (GraphAdjacencyProgram.steps u v+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 34) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (adjacent rows u v)) := by
  obtain ⟨ext,root,len,core,flag⟩ := GraphAdjacencyProgram.read_return input context hi hj
    next c d hn ⟨a,b,c,d⟩ 35 [] source
  have call : tickNatural GraphAdjacencyProgram.program
      (GraphAdjacencyProgram.state heap next a b c d [] source 34)=
      some ⟨GraphAdjacencyProgram.state heap next a b c d [⟨35,.r3,⟨a,b,c,d⟩⟩] source 27,[],0⟩ := by
    simp [tickNatural,GraphAdjacencyProgram.program,GraphAdjacencyProgram.state]
  have lift := ReferenceProgramLabels.run adjLabel GraphAdjacencyProgram.program program adj_slots (.step call core)
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (GraphAdjacencyProgram.steps u v+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 34) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 35) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      GraphAdjacencyProgram.state,adjLabel,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 35)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,run_append body (.step ret (.done _)),?_⟩
  simpa [adjacent,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using flag

theorem extension_lift {heap ext : NaturalHeap} {a b c d root next k : ℕ} {source : Bits}
    (core : NaturalRun GraphWalkExtension.program k
      (GraphWalkExtension.state heap next a b c d [] source 268) []
      (GraphWalkExtension.state (heap++ext) (next+ext.length) a b c root [] source 269))
    (frames : List (Frame ℕ 532)) :
    NaturalRun program k (state heap next a b c d frames source 304) []
      (state (heap++ext) (next+ext.length) a b c root frames source 305) := by
  have lift := ReferenceProgramLabels.run extLabel GraphWalkExtension.program program ext_slots core
  have lift := ReferenceProgramStack.run program frames lift
  simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
    GraphWalkExtension.state,extLabel,state] using lift

theorem extension_return {heap : NaturalHeap} {a b c : ℕ} {e : Bits×Bits} {q : Walk}
    {rows : List Fraction} {sw : Bits} (edge : Edge heap a e) (walk : StoredWalk heap b q)
    (context : OutgoingCostProgram.Context heap c rows sw) (hi : value e.1<rows.length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 532) (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext root,ext.length=GraphWalkExtension.cells rows sw e q ∧
      NaturalRun program (GraphWalkExtension.steps rows sw e q+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 304) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredWalk (heap++ext) root (GraphWalkExtension.result rows sw e q) := by
  obtain ⟨ext,root,len,core,rep⟩ := GraphWalkExtension.extend_high edge walk context hi next d hn source
  have body := extension_lift core (⟨pc,.r3,saved⟩::stack)
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 305)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  simpa only [Nat.add_assoc,List.nil_append] using run_append body (.step ret (.done _))

theorem rational_return (x y : BinaryRational.Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : RationalComparisonProgram.Stored heap a x) (right : RationalComparisonProgram.Stored heap b y)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 532)
    (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext root,ext.length=RationalComparisonProgram.cells x y ∧
      NaturalRun program (RationalComparisonProgram.instructions x y+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 450) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (BinaryRational.le x y).1) := by
  obtain ⟨u,run,flag,_,_,src,frames,hpc,dense,ext,_⟩ :=
    RationalComparisonProgram.run_high x y (RationalComparisonProgram.state heap next a b c d [] source 144)
      rfl hn left right rfl
  obtain ⟨ext,he,le⟩ := ext
  have lifted := ReferenceProgramLabels.run cmpLabel RationalComparisonProgram.program program cmp_slots run
  have lifted := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lifted
  have body : NaturalRun program (RationalComparisonProgram.instructions x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 450) []
      (state (heap++ext) (next+ext.length) u.registers.a u.registers.b u.registers.c u.registers.d
        (⟨pc,.r3,saved⟩::stack) source 463) := by
    have un : u.next=next+ext.length := by rw [dense,he];simp [RationalComparisonProgram.state,hn]
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      RationalComparisonProgram.state,cmpLabel,state,he,un,src,frames,hpc] using lifted
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) u.registers.a u.registers.b u.registers.c u.registers.d
        (⟨pc,.r3,saved⟩::stack) source 463)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c u.registers.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,u.registers.d,le,?_,?_⟩
  · simpa using run_append body (.step ret (.done _))
  · simpa only [he,RationalComparisonProgram.state] using flag

end DirectedFlowCutGap.GraphRelaxationProgram
