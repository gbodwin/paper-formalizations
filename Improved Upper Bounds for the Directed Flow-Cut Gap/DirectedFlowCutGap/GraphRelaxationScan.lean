import DirectedFlowCutGap.GraphRelaxationFinish

/-! A literal recursive scan of represented old walk records. Its adjacency
reads, accepted-edge allocations, rational extensions and stable comparisons
all occur in one fixed instruction program and one shared immutable heap. -/
namespace DirectedFlowCutGap.GraphRelaxationProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem scan_return {heap : NaturalHeap} {a b : ℕ} {xs : List Entry}
    {adjacency : List Bits} {rows : List Fraction} {u sw : Bits}
    (table : Table heap a xs) (context : Context heap b adjacency rows u sw)
    (hi : value u<adjacency.length) (hc : value u<rows.length)
    (hcols : ∀ x∈xs,value x.1<(adjacency[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 532) (stack : List (Frame ℕ 532)) (source : Bits) :
    ∃ ext root,ext.length=cells adjacency rows sw u xs ∧
      NaturalRun program (steps adjacency rows sw u xs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 464) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (scan adjacency rows sw u xs) := by
  induction table generalizing c saved pc stack with
  | @nil p hp =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have t464 : tickNatural program (state heap next p b c d frames source 464)=
        some ⟨state heap next p b c d frames source 465,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t465 : tickNatural program (state heap next p b c d frames source 465)=
        some ⟨state (heap++[.nil]) (next+1) p b c next frames source 466,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural]
    have t466 : tickNatural program (state (heap++[.nil]) (next+1) p b c next frames source 466)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨[.nil],next,rfl,?_,?_⟩
    · simpa [steps] using NaturalRun.step t464 (.step t465 (.step t466 (.done _)))
    · simp [scan,StoredOption,hn]
  | @cons p head tail x xs hp hx ht ih =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have htail : ∀ y∈xs,value y.1<(adjacency[value u]).length := fun y hy => hcols y (by simp [hy])
    obtain ⟨et,rt,lt,runT,repT⟩ := ih htail head ⟨tail,b,head,d⟩ 470 frames
    let h0 := heap++et
    let n0 := next+et.length
    let e0 : NaturalHeap := [.pair head rt]
    let h1 := h0++e0
    let n1 := n0+1
    have dense0 : n0=h0.length := by simp [h0,n0,hn]
    have dense1 : n1=h1.length := by simp [h1,n1,e0,dense0]
    have scratch : h1[n0]?=some (.pair head rt) := by simp [h1,e0,dense0]
    obtain ⟨ea,ra,la,runA,flagA⟩ := test_return (entry_extend (entry_extend hx et) e0)
      (context_extend (context_extend context et) e0) hi (hcols x (by simp))
      n1 n0 rt dense1 ⟨head,b,n0,rt⟩ 473 frames source
    let h2 := h1++ea
    let n2 := n1+ea.length
    have dense2 : n2=h2.length := by simp [h2,n2,dense1]
    obtain ⟨ef,rf,lf,runF,repF⟩ := finish_return
      (entry_extend (entry_extend (entry_extend hx et) e0) ea)
      (context_extend (context_extend (context_extend context et) e0) ea)
      (lookup_extend scratch ea) (option_extend (option_extend repT e0) ea) flagA hc
      n2 dense2 saved pc stack source
    have t464 : tickNatural program (state heap next p b c d frames source 464)=
        some ⟨state heap next p b c d frames source 467,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t467 : tickNatural program (state heap next p b c d frames source 467)=
        some ⟨state heap next p b head d frames source 468,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t468 : tickNatural program (state heap next p b head d frames source 468)=
        some ⟨state heap next tail b head d frames source 469,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t469 : tickNatural program (state heap next tail b head d frames source 469)=
        some ⟨state heap next tail b head d (⟨470,.r3,⟨tail,b,head,d⟩⟩::frames) source 464,[],0⟩ := by
      simp [tickNatural,program,state]
    have t470 : tickNatural program (state h0 n0 tail b head rt frames source 470)=
        some ⟨state h1 n1 tail b n0 rt frames source 471,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h1,n1,e0]
    have t471 : tickNatural program (state h1 n1 tail b n0 rt frames source 471)=
        some ⟨state h1 n1 head b n0 rt frames source 472,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t472 : tickNatural program (state h1 n1 head b n0 rt frames source 472)=
        some ⟨state h1 n1 head b n0 rt (⟨473,.r3,⟨head,b,n0,rt⟩⟩::frames) source 500,[],0⟩ := by
      simp [tickNatural,program,state]
    let ext := et++e0++ea++ef
    have shape : heap++ext=h2++ef := by simp [ext,h2,h1,h0,List.append_assoc]
    have count : next+ext.length=n2+ef.length := by simp [ext,n2,n1,n0,e0];omega
    refine ⟨ext,rf,?_,?_,?_⟩
    · simp only [ext,List.length_append,lt,la,lf,e0,List.length_cons,List.length_nil]
      simp only [cells,finishCells,optionCells]
      split_ifs <;> rfl
    · have first := NaturalRun.step t464 (.step t467 (.step t468 (.step t469 runT)))
      have second := NaturalRun.step t470 (.step t471 (.step t472 (run_append runA runF)))
      have joined := run_append first second
      rw [shape,count]
      convert joined using 1
      simp only [steps,finishSteps,optionSteps]
      split_ifs <;> cases scan adjacency rows sw u xs <;> (try simp) <;> omega
      all_goals rfl
    · rw [shape]
      simpa only [scan] using repF

end DirectedFlowCutGap.GraphRelaxationProgram
