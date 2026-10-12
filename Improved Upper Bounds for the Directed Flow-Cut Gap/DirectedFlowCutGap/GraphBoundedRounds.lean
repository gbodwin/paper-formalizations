import DirectedFlowCutGap.GraphRoundCalls

/-! Successive rounds consume the actual retained fuel spine. Every old table
passed to relaxation was constructed by the preceding part of this same run. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem rounds_return {heap : NaturalHeap} {a b : ℕ} {fuel vertices adjacency : List Bits}
    {rows : List Fraction} {sw target : Bits}
    (input : Vertices heap a fuel) (context : GlobalContext heap b vertices adjacency rows sw target)
    (hi : ∀ u∈vertices,value u<adjacency.length) (hc : ∀ u∈vertices,value u<rows.length)
    (targetCol : ∀ u,(hu : u∈vertices) → value target<(adjacency[value u]'(hi u hu)).length)
    (columns : ∀ u,(hu : u∈vertices) → ∀ v∈vertices,value v<(adjacency[value u]'(hi u hu)).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=roundCells vertices adjacency rows sw target fuel ∧
      NaturalRun program (roundSteps vertices adjacency rows sw target fuel)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 660) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Table (heap++ext) root (rounds vertices adjacency rows sw target fuel) := by
  induction input generalizing saved pc stack with
  | @nil p hp =>
    obtain ⟨tr,bundle,enumRoot,mix,matrix,cost,hb,_,_,ht,_,_,_⟩ := context
    obtain ⟨ext,root,len,body,rep⟩ := initial_table hb ht next p c d hn saved pc stack source
    have first : tickNatural program (state heap next p b c d (⟨pc,.r3,saved⟩::stack) source 660)=
        some ⟨state heap next p b c d (⟨pc,.r3,saved⟩::stack) source 661,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    exact ⟨ext,root,len,by simpa [roundSteps] using NaturalRun.step first body,rep⟩
  | @cons p head tail u us hp hu ht ih =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    obtain ⟨et,rt,lt,runT,repT⟩ := ih ⟨tail,b,c,d⟩ 672 frames
    let h0 := heap++et
    let n0 := next+et.length
    have dense : n0=h0.length := by simp [h0,n0,hn]
    have hcols : ∀ v,(hv : v∈vertices) → ∀ x∈rounds vertices adjacency rows sw target us,
        value x.1<(adjacency[value v]'(hi v hv)).length := by
      intro v hv x hx
      rcases round_label us hx with he|he
      · rw [he];exact targetCol v hv
      · exact columns v hv x.1 he
    obtain ⟨ep,rp,lp,runP,repP⟩ := next_pass (global_extend context et) repT hi hc hcols
      n0 tail c dense saved pc stack source
    have t660 : tickNatural program (state heap next p b c d frames source 660)=
        some ⟨state heap next p b c d frames source 670,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t670 : tickNatural program (state heap next p b c d frames source 670)=
        some ⟨state heap next tail b c d frames source 671,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t671 : tickNatural program (state heap next tail b c d frames source 671)=
        some ⟨state heap next tail b c d (⟨672,.r3,⟨tail,b,c,d⟩⟩::frames) source 660,[],0⟩ := by
      simp [tickNatural,program,state]
    refine ⟨et++ep,rp,?_,?_,?_⟩
    · simp [roundCells,lt,lp,Nat.add_assoc]
    · have joined := NaturalRun.step t660 (.step t670 (.step t671 (run_append runT runP)))
      convert joined using 1 <;>
        simp [roundSteps,n0,List.append_assoc,Nat.add_assoc]
    · simpa [rounds,h0,List.append_assoc] using repP

end DirectedFlowCutGap.GraphDiscoveryProgram
