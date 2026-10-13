import DirectedFlowCutGap.GridInputCalls

namespace DirectedFlowCutGap.GridInputProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

set_option maxRecDepth 10000 in
theorem prepare_return {rows : List Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 544)
    (stack : List (Frame ℕ 544)) (source : Bits) :
    ∃ ext root,ext.length=cells rows ∧
      NaturalRun program (steps rows)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 500) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Prepared (heap++ext) root rows := by
  let frame : Frame ℕ 544 := ⟨pc,.r3,saved⟩
  obtain ⟨ew,wroot,wlen,wrun,wrep⟩ := width_call input next b a d dense ⟨a,b,a,d⟩ 502 (frame::stack) source
  obtain ⟨en,droot,nlen,nrun,nrep⟩ := dimension_call (BinaryIndexedPairRead.table_extend input ew)
    (next+ew.length) wroot a wroot (by simp [dense]) ⟨a,wroot,a,wroot⟩ 505 (frame::stack) source
  obtain ⟨ef,froot,flen,frun,frep⟩ := fuel_call nrep (boolList_extend wrep en)
    (next+ew.length+en.length) a droot (by simp [dense,Nat.add_assoc])
    ⟨droot,wroot,a,droot⟩ 507 (frame::stack) source
  let H := ((heap++ew)++en)++ef
  let N := next+ew.length+en.length+ef.length
  let cellsOut : NaturalHeap := [.pair droot wroot,.pair N froot]
  have hnH : N=H.length := by simp [N,H,dense,Nat.add_assoc]
  have t500 : tickNatural program (state heap next a b c d (frame::stack) source 500)=
      some ⟨state heap next a b a d (frame::stack) source 501,[],0⟩ := by rfl
  have t501 : tickNatural program (state heap next a b a d (frame::stack) source 501)=
      some ⟨state heap next a b a d (⟨502,.r3,⟨a,b,a,d⟩⟩::frame::stack) source 206,[],0⟩ := by rfl
  have t502 : tickNatural program (state (heap++ew) (next+ew.length) a b a wroot (frame::stack) source 502)=
      some ⟨state (heap++ew) (next+ew.length) a wroot a wroot (frame::stack) source 503,[],0⟩ := by rfl
  have t503 : tickNatural program (state (heap++ew) (next+ew.length) a wroot a wroot (frame::stack) source 503)=
      some ⟨state (heap++ew) (next+ew.length) a wroot a wroot (frame::stack) source 504,[],0⟩ := by rfl
  have t504 : tickNatural program (state (heap++ew) (next+ew.length) a wroot a wroot (frame::stack) source 504)=
      some ⟨state (heap++ew) (next+ew.length) a wroot a wroot
        (⟨505,.r3,⟨a,wroot,a,wroot⟩⟩::frame::stack) source 224,[],0⟩ := by rfl
  have t505 : tickNatural program (state ((heap++ew)++en) (next+ew.length+en.length) a wroot a droot (frame::stack) source 505)=
      some ⟨state ((heap++ew)++en) (next+ew.length+en.length) droot wroot a droot (frame::stack) source 506,[],0⟩ := by rfl
  have t506 : tickNatural program (state ((heap++ew)++en) (next+ew.length+en.length) droot wroot a droot (frame::stack) source 506)=
      some ⟨state ((heap++ew)++en) (next+ew.length+en.length) droot wroot a droot
        (⟨507,.r3,⟨droot,wroot,a,droot⟩⟩::frame::stack) source 486,[],0⟩ := by rfl
  have t507 : tickNatural program (state H N droot wroot a froot (frame::stack) source 507)=
      some ⟨state (H++[.pair droot wroot]) (N+1) droot N a froot (frame::stack) source 508,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
  have t508 : tickNatural program (state (H++[.pair droot wroot]) (N+1) droot N a froot (frame::stack) source 508)=
      some ⟨state (H++cellsOut) (N+2) droot N a (N+1) (frame::stack) source 509,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,cellsOut,List.append_assoc,Nat.add_assoc]
  have t509 : tickNatural program (state (H++cellsOut) (N+2) droot N a (N+1) (frame::stack) source 509)=
      some ⟨state (H++cellsOut) (N+2) saved.a saved.b saved.c (N+1) stack source pc,[],0⟩ := by
    simp [program,tickNatural,state,frame,Registers.get,Registers.set]
  refine ⟨ew++en++ef++cellsOut,N+1,?_,?_,?_⟩
  · simp [cells,wlen,nlen,flen,cellsOut,Nat.add_assoc];omega
  · have all := NaturalRun.step t500 (NaturalRun.step t501 (run_append wrun (NaturalRun.step t502 (NaturalRun.step t503 (NaturalRun.step t504 (run_append nrun (NaturalRun.step t505 (NaturalRun.step t506 (run_append frun (NaturalRun.step t507 (NaturalRun.step t508 (NaturalRun.step t509 (.done _)))))))))))))
    convert all using 1 <;> simp [steps,state,H,N,cellsOut,List.append_assoc,Nat.add_assoc]; omega
  · have hd : BoolList (H++cellsOut) droot (dimension rows) := boolList_extend (boolList_extend nrep ef) cellsOut
    have hw : BoolList (H++cellsOut) wroot (width rows) := boolList_extend (boolList_extend (boolList_extend wrep en) ef) cellsOut
    have hf := boolList_extend frep cellsOut
    have hp : Prepared (H++cellsOut) (N+1) rows :=
      ⟨N,droot,wroot,froot,by simp [cellsOut,hnH],by simp [cellsOut,hnH],hd,hw,hf⟩
    simpa [H,List.append_assoc] using hp
end DirectedFlowCutGap.GridInputProgram
