import DirectedFlowCutGap.GraphLookupDecision

/-! Literal tail-first lookup of the constructed walk table. Numeric padded
label equality and stable rational first ties are both executed by instructions. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem lookup_return {heap : NaturalHeap} {a b : ℕ} {xs : List Entry} {u : Bits}
    (table : Table heap a xs) (word : BoolList heap b u)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=lookupCells u xs ∧ NaturalRun program (lookupSteps u xs)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 680) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (lookup u xs) := by
  induction table generalizing c saved pc stack with
  | @nil p hp =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have t680 : tickNatural program (state heap next p b c d frames source 680)=
        some ⟨state heap next p b c d frames source 681,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t681 : tickNatural program (state heap next p b c d frames source 681)=
        some ⟨state (heap++[.nil]) (next+1) p b c next frames source 682,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
    have t682 : tickNatural program (state (heap++[.nil]) (next+1) p b c next frames source 682)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨[.nil],next,rfl,?_,?_⟩
    · exact .step t680 (.step t681 (.step t682 (.done _)))
    · simp [lookup,StoredOption,GraphRelaxationProgram.StoredOption,hn]
  | @cons p head tail x xs hp hx ht ih =>
    obtain ⟨vertex,walk,hhead,hvertex,hwalk⟩ := hx
    have hx : GraphRelaxationProgram.StoredEntry heap head x := ⟨vertex,walk,hhead,hvertex,hwalk⟩
    let frames := (⟨pc,.r3,saved⟩::stack)
    obtain ⟨et,rt,lt,runT,repT⟩ := ih head ⟨tail,b,head,d⟩ 686 frames
    let h0 := heap++et
    let n0 := next+et.length
    let e0 : NaturalHeap := [.pair head rt]
    let h1 := h0++e0
    let n1 := n0+1
    have dense0 : n0=h0.length := by simp [h0,n0,hn]
    have dense1 : n1=h1.length := by simp [h1,n1,e0,dense0]
    have scratch : h1[n0]?=some (.pair head rt) := by simp [h1,e0,dense0]
    obtain ⟨ec,rc,lc,runC,tagC⟩ := compare_return
      (boolList_extend (boolList_extend hvertex et) e0)
      (boolList_extend (boolList_extend word et) e0) n1 n0 rt dense1 ⟨vertex,b,n0,rt⟩ 690 frames source
    let h2 := h1++ec
    let n2 := n1+ec.length
    have dense2 : n2=h2.length := by simp [h2,n2,dense1]
    obtain ⟨ef,rf,lf,runF,repF⟩ := lookup_decision
      (GraphRelaxationProgram.entry_extend (GraphRelaxationProgram.entry_extend (GraphRelaxationProgram.entry_extend hx et) e0) ec)
      (GraphRelaxationProgram.option_extend (GraphRelaxationProgram.option_extend repT e0) ec)
      (lookup_extend scratch ec) tagC n2 vertex b dense2 saved pc stack source
    have t680 : tickNatural program (state heap next p b c d frames source 680)=
        some ⟨state heap next p b c d frames source 683,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t683 : tickNatural program (state heap next p b c d frames source 683)=
        some ⟨state heap next p b head d frames source 684,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t684 : tickNatural program (state heap next p b head d frames source 684)=
        some ⟨state heap next tail b head d frames source 685,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t685 : tickNatural program (state heap next tail b head d frames source 685)=
        some ⟨state heap next tail b head d (⟨686,.r3,⟨tail,b,head,d⟩⟩::frames) source 680,[],0⟩ := by
      simp [tickNatural,program,state]
    have t686 : tickNatural program (state h0 n0 tail b head rt frames source 686)=
        some ⟨state h1 n1 tail b n0 rt frames source 687,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1,n1,e0]
    have t687 : tickNatural program (state h1 n1 tail b n0 rt frames source 687)=
        some ⟨state h1 n1 head b n0 rt frames source 688,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t688 : tickNatural program (state h1 n1 head b n0 rt frames source 688)=
        some ⟨state h1 n1 vertex b n0 rt frames source 689,[],0⟩ := by
      have oldhead : h1[head]?=some (.pair vertex walk) := lookup_extend (lookup_extend hhead et) e0
      simp [tickNatural,program,state,Registers.get,Registers.set,oldhead]
    have t689 : tickNatural program (state h1 n1 vertex b n0 rt frames source 689)=
        some ⟨state h1 n1 vertex b n0 rt (⟨690,.r3,⟨vertex,b,n0,rt⟩⟩::frames) source 580,[],0⟩ := by
      simp [tickNatural,program,state]
    let ext := et++e0++ec++ef
    have shape : heap++ext=h2++ef := by simp [ext,h2,h1,h0,List.append_assoc]
    have count : next+ext.length=n2+ef.length := by simp [ext,n2,n1,n0,e0];omega
    refine ⟨ext,rf,?_,?_,?_⟩
    · simp only [ext,List.length_append,lt,lc,lf,e0,List.length_cons,List.length_nil,
        lookupCells,lookupDecisionCells]
    · have first := NaturalRun.step t680 (.step t683 (.step t684 (.step t685 runT)))
      have second := NaturalRun.step t686 (.step t687 (.step t688 (.step t689 (run_append runC runF))))
      rw [shape,count]
      convert run_append first second using 1 <;> try rfl
      simp only [lookupSteps,lookupDecisionSteps]
      split_ifs <;> omega
    · rw [shape];simpa only [lookup] using repF

end DirectedFlowCutGap.GraphDiscoveryProgram
