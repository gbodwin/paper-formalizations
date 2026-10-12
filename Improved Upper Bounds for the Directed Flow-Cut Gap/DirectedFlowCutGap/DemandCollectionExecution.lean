import DirectedFlowCutGap.DemandCollectionStep

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem collect_return {heap : NaturalHeap} {p : ℕ} {xs : List Demand}
    {vs adjacency : List Bits} {values : List Fraction} (N : ℕ)
    (input : DemandList heap p xs)
    (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (hc : ∀ v∈vs,value v<values.length)
    (valid : ∀ x∈xs,value x.targetWord<N ∧
      ∀ q,GraphDiscoveryProgram.minimize vs adjacency values x.sourceWord x.targetWord x.sourceWord=some q →
        ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges x.sourceWord x.targetWord).map Prod.fst,value w<values.length)
    (next b c d : ℕ) (hn : next=heap.length) (shared : Shared heap b vs adjacency values)
    (saved : Registers ℕ) (pc : Fin 1604) (stack : List (Frame ℕ 1604)) (source : Bits) :
    ∃ ext root,ext.length=cells vs adjacency values xs ∧
      NaturalRun program (steps vs adjacency values xs)
        (state heap next p b c d (⟨pc,.r3,saved⟩::stack) source 1540) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      RecordList (heap++ext) root (records vs adjacency values next xs) := by
  induction input generalizing next b c d saved pc stack with
  | @nil p hp =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have t1540 : tickNatural program (state heap next p b c d frames source 1540)=
        some ⟨state heap next p b c d frames source 1541,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t1541 : tickNatural program (state heap next p b c d frames source 1541)=
        some ⟨state (heap++[.nil]) (next+1) p b c next frames source 1542,[],0⟩ := by
      simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
    have t1542 : tickNatural program (state (heap++[.nil]) (next+1) p b c next frames source 1542)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨[.nil],next,rfl,.step t1540 (.step t1541 (.step t1542 (.done _))),.nil (by simp [hn])⟩
  | @cons p tail x xs he hp hx hxs ih =>
    subst p
    let frames := (⟨pc,.r3,saved⟩::stack)
    have vx := valid x (by simp)
    have vsound : ∀ y∈xs,value y.targetWord<N ∧
        ∀ q,GraphDiscoveryProgram.minimize vs adjacency values y.sourceWord y.targetWord y.sourceWord=some q →
          ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges y.sourceWord y.targetWord).map Prod.fst,value w<values.length :=
      fun y hy => valid y (by simp [hy])
    obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih vsound next b x.occurrence d hn shared
      ⟨tail,b,x.occurrence,d⟩ 1546 frames
    let h1 := heap++et
    let n1 := next+et.length
    have dense1 : n1=h1.length := by simp [n1,h1,hn]
    obtain ⟨eh,rh,lh,headRun,headRep⟩ := step_return N (lookup_extend hp et) (demand_extend hx et)
      (shared_extend shared et) tailRep rows cols hv vx.1 hc vx.2
      n1 tail dense1 saved pc stack source
    have t1540 : tickNatural program (state heap next x.occurrence b c d frames source 1540)=
        some ⟨state heap next x.occurrence b c d frames source 1543,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t1543 : tickNatural program (state heap next x.occurrence b c d frames source 1543)=
        some ⟨state heap next x.occurrence b x.occurrence d frames source 1544,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t1544 : tickNatural program (state heap next x.occurrence b x.occurrence d frames source 1544)=
        some ⟨state heap next tail b x.occurrence d frames source 1545,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t1545 : tickNatural program (state heap next tail b x.occurrence d frames source 1545)=
        some ⟨state heap next tail b x.occurrence d (⟨1546,.r3,⟨tail,b,x.occurrence,d⟩⟩::frames) source 1540,[],0⟩ := by
      simp [tickNatural,program,state]
    refine ⟨et++eh,rh,?_,?_,?_⟩
    · cases hq : query vs adjacency values x <;> simp [cells,lt,lh,hq,Nat.add_assoc]
    · have all := run_append (.step t1540 (.step t1543 (.step t1544 (.step t1545 tailRun)))) headRun
      cases hq : query vs adjacency values x <;>
        convert all using 1 <;> simp [steps,n1,List.append_assoc,hq,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
    · have eqRecords : stepRecords vs adjacency values n1 x (records vs adjacency values next xs)=
          records vs adjacency values next (x::xs) := by
        cases hq : query vs adjacency values x <;> simp [stepRecords,records,n1,lt,hq,Nat.add_assoc]
      simpa only [h1,List.append_assoc,eqRecords] using headRep

end DirectedFlowCutGap.DemandCollection
