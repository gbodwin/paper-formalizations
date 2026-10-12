import DirectedFlowCutGap.SupportRoundInitial

/-! The finite fuel list drives actual calls; every pass consumes the table
constructed by its preceding recursive call. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem rounds_return {heap : NaturalHeap} {a b : ℕ} {vs adjacency fuel : List Bits}
    {es : List (Bits × Bits)} {target : Bits} (N : ℕ)
    (input : Vertices heap a fuel) (context : StoredGlobalContext heap b vs adjacency es target)
    (rows : N≤adjacency.length) (cols : ∀ (i : ℕ) (hi : i<N), N≤(adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (ht : value target<N)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=roundCells vs adjacency es target fuel ∧
      NaturalRun program (roundSteps vs adjacency es target fuel)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 240) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Codes (heap++ext) root (rounds vs adjacency es target fuel) := by
  induction fuel generalizing heap a b next c d saved pc stack with
  | nil =>
    cases input with
    | nil hp =>
      obtain ⟨ext,root,len,body,out⟩ := initial_return hp context next c d hn saved pc stack source
      exact ⟨ext,root,len,by simpa [roundSteps,len] using body,by simpa [rounds] using out⟩
  | cons u us ih =>
    cases input with
    | @cons _ head tail _ _ hp _ htail =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      obtain ⟨e1,oldtable,len1,recursive,oldcodes⟩ := ih htail context next c d hn
        ⟨tail,b,c,d⟩ 248 frames
      obtain ⟨tr,bundle,vertices,supp,hb,hbundle,htr,hvs,hsupp⟩ := context
      let e2 : NaturalHeap := [.pair oldtable supp]
      have passctx : StoredVisitContext ((heap++e1)++e2) (next+e1.length)
          adjacency es (rounds vs adjacency es target us) := by
        exact ⟨oldtable,supp,by simp [e2,hn],codes_extend oldcodes e2,
          supportContext_extend (supportContext_extend hsupp e1) e2⟩
      obtain ⟨e3,root,len3,body,out⟩ := pass_return N
        (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend hvs e1) e2)
        passctx rows cols hv (rounds_valid vs adjacency es target us N hv ht)
        (next+e1.length+1) supp oldtable (by simp [e2,hn];omega)
        ⟨vertices,next+e1.length,supp,oldtable⟩ 253 frames source
      have t240 : tickNatural program (state heap next a b c d frames source 240)=
          some ⟨state heap next a b c d frames source 246,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t246 : tickNatural program (state heap next a b c d frames source 246)=
          some ⟨state heap next tail b c d frames source 247,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t247 : tickNatural program (state heap next tail b c d frames source 247)=
          some ⟨state heap next tail b c d (⟨248,.r3,⟨tail,b,c,d⟩⟩::frames) source 240,[],0⟩ := by
        simp [tickNatural,program,state]
      have t248 : tickNatural program (state (heap++e1) (next+e1.length) tail b c oldtable frames source 248)=
          some ⟨state (heap++e1) (next+e1.length) bundle b c oldtable frames source 249,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hb e1]
      have t249 : tickNatural program (state (heap++e1) (next+e1.length) bundle b c oldtable frames source 249)=
          some ⟨state (heap++e1) (next+e1.length) bundle b supp oldtable frames source 250,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hbundle e1]
      have t250 : tickNatural program (state (heap++e1) (next+e1.length) bundle b supp oldtable frames source 250)=
          some ⟨state (heap++e1) (next+e1.length) vertices b supp oldtable frames source 251,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hbundle e1]
      have t251 : tickNatural program (state (heap++e1) (next+e1.length) vertices b supp oldtable frames source 251)=
          some ⟨state ((heap++e1)++e2) (next+e1.length+1) vertices (next+e1.length) supp oldtable frames source 252,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,e2]
      have t252 : tickNatural program
          (state ((heap++e1)++e2) (next+e1.length+1) vertices (next+e1.length) supp oldtable frames source 252)=
          some ⟨state ((heap++e1)++e2) (next+e1.length+1) vertices (next+e1.length) supp oldtable
            (⟨253,.r3,⟨vertices,next+e1.length,supp,oldtable⟩⟩::frames) source 220,[],0⟩ := by
        simp [tickNatural,program,state]
      have t253 : tickNatural program
          (state (((heap++e1)++e2)++e3) (next+e1.length+1+e3.length) vertices (next+e1.length) supp root frames source 253)=
          some ⟨state (((heap++e1)++e2)++e3) (next+e1.length+1+e3.length)
            saved.a saved.b saved.c root stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      refine ⟨e1++e2++e3,root,by simp [roundCells,e2,len1,len3];omega,?_,?_⟩
      · convert (NaturalRun.step t240 (.step t246 (.step t247 (run_append recursive
          (.step t248 (.step t249 (.step t250 (.step t251 (.step t252
            (run_append body (.step t253 (.done _)))))))))))) using 1 <;>
          simp [roundSteps,e2,List.append_assoc,state]
        all_goals omega
      · simpa [rounds,List.append_assoc] using out

end DirectedFlowCutGap.SupportRecoveryProgram
