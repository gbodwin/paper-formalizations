import DirectedFlowCutGap.GraphDiscoveryProgram

/-! Real caller-preserving comparison, relaxation and target-zero allocation. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem compare_return {u target : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a u) (right : BoolList heap b target) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root, ext.length=BinaryComparisonProgram.cells u target ∧
      NaturalRun program (BinaryComparisonProgram.steps u target+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 580) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order u target)) := by
  obtain ⟨ext,root,len,body,tag⟩ := BinaryComparisonProgram.compare_return
    left right next c d hn ⟨a,b,c,d⟩ 47 [] source
  have lift := ReferenceProgramLabels.run cmpLabel BinaryComparisonProgram.program program cmp_slots body
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have core : NaturalRun program (BinaryComparisonProgram.steps u target)
      (state heap next a b c d (⟨579,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 532) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 579) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryComparisonProgram.state,cmpLabel,state] using lift
  have first : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 580)=
      some ⟨state heap next a b c d (⟨579,.r3,⟨a,b,c,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 532,[],0⟩ := by
    simp [tickNatural,program,state]
  have last : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 579)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using (NaturalRun.step first
        (run_append core (.step last (.done _)))),tag⟩

theorem scan_return {adjacency : List Bits} {rows : List Fraction} {sw u : Bits} {xs : List Entry}
    {heap : NaturalHeap} {a b : ℕ} (input : Table heap a xs)
    (context : GraphRelaxationProgram.Context heap b adjacency rows u sw)
    (hi : value u<adjacency.length) (hc : value u<rows.length)
    (hcols : ∀ x∈xs,value x.1<(adjacency[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=GraphRelaxationProgram.cells adjacency rows sw u xs ∧
      NaturalRun program (GraphRelaxationProgram.steps adjacency rows sw u xs+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 530) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (GraphRelaxationProgram.scan adjacency rows sw u xs) := by
  obtain ⟨ext,root,len,body,rep⟩ := GraphRelaxationProgram.scan_high
    (GraphRelaxationProgram.state heap next a b c d [] source 530) rfl hn rfl input context hi hc hcols
  have lift := ReferenceProgramLabels.run scanLabel GraphRelaxationProgram.program program scan_slots body
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have core : NaturalRun program (GraphRelaxationProgram.steps adjacency rows sw u xs+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 530) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 531) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      GraphRelaxationProgram.state,scanLabel,state] using lift
  have last : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 531)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append core (.step last (.done _)),rep⟩

/-- The empty target walk and its literal rational zero share the newly
allocated nil, but every flag, spine and record cell is genuinely paid. -/
theorem zero_return (heap : NaturalHeap) (next a b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 720) (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=5 ∧ NaturalRun program 6
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 590) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredWalk (heap++ext) root zero := by
  let ext : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair next (next+2),.pair next (next+3)]
  let frames := (⟨pc,.r3,saved⟩::stack)
  have t590 : tickNatural program (state heap next a b c d frames source 590)=
      some ⟨state (heap++[.nil]) (next+1) a b c next frames source 591,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
  have t591 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 591)=
      some ⟨state (heap++[.nil,.flag true]) (next+2) (next+1) b c next frames source 592,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,List.append_assoc]
  have t592 : tickNatural program (state (heap++[.nil,.flag true]) (next+2) (next+1) b c next frames source 592)=
      some ⟨state (heap++[.nil,.flag true,.pair (next+1) next]) (next+3) (next+2) b c next frames source 593,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,List.append_assoc]
  have t593 : tickNatural program (state (heap++[.nil,.flag true,.pair (next+1) next]) (next+3) (next+2) b c next frames source 593)=
      some ⟨state (heap++[.nil,.flag true,.pair (next+1) next,.pair next (next+2)]) (next+4)
        (next+2) b (next+3) next frames source 594,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,List.append_assoc]
  have t594 : tickNatural program
      (state (heap++[.nil,.flag true,.pair (next+1) next,.pair next (next+2)]) (next+4)
        (next+2) b (next+3) next frames source 594)=
      some ⟨state (heap++ext) (next+5) (next+2) b (next+3) (next+4) frames source 595,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,List.append_assoc,ext]
  have t595 : tickNatural program
      (state (heap++ext) (next+5) (next+2) b (next+3) (next+4) frames source 595)=
      some ⟨state (heap++ext) (next+5) saved.a saved.b saved.c (next+4) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨ext,next+4,rfl,?_,?_⟩
  · exact .step t590 (.step t591 (.step t592 (.step t593 (.step t594 (.step t595 (.done _))))))
  · refine ⟨next,next+3,?_,.nil ?_,next,next+2,?_,.nil ?_,
      .cons (head:=next+1) (tail:=next) ?_ ?_ (.nil ?_)⟩ <;> simp [ext,hn]

end DirectedFlowCutGap.GraphDiscoveryProgram
