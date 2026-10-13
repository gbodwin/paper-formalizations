import DirectedFlowCutGap.GridFuelConstants

namespace DirectedFlowCutGap.GridFuelProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

set_option maxRecDepth 10000 in
theorem fuel_return {dimension width : Bits} {heap : NaturalHeap} {a b : ℕ}
    (dim : BoolList heap a dimension) (wid : BoolList heap b width)
    (next c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 256)
    (stack : List (Frame ℕ 256)) (source : Bits) :
    ∃ ext root,ext.length=cells dimension width ∧
      NaturalRun program (steps dimension width)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 200) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.gridFuel dimension width).1 := by
  let frame : Frame ℕ 256 := ⟨pc,.r3,saved⟩
  obtain ⟨en,sroot,nlen,nrun,nrep⟩ := size_call dim next b a d dense ⟨a,b,a,d⟩ 202 (frame::stack) source
  let N0 := next+en.length
  let H0 := heap++en
  let e2 := twoCells N0
  obtain ⟨twoRun,twoRep⟩ := two_prefix H0 N0 a b sroot sroot (by simp [H0,N0,dense]) (frame::stack) source
  obtain ⟨ew,wroot,wlen,wrun,wrep⟩ := arithmetic_call true twoRep (boolList_extend (boolList_extend wid en) e2)
    (N0+5) sroot (N0+3) (by simp [H0,N0,twoCells,dense,Nat.add_assoc])
    ⟨N0+4,b,sroot,N0+3⟩ 209 (frame::stack) source
  let H1 := (H0++e2)++ew
  let N1 := N0+5+ew.length
  obtain ⟨er,nroot,rlen,rrun,rrep⟩ := arithmetic_call true (boolList_extend twoRep ew)
    (boolList_extend (boolList_extend nrep e2) ew) N1 wroot wroot
    (by simp [N1,H0,N0,twoCells,dense,Nat.add_assoc];omega)
    ⟨N0+4,sroot,wroot,wroot⟩ 212 (frame::stack) source
  let H2 := H1++er
  let N2 := N1+er.length
  obtain ⟨es,sroot',slen,srun,srep⟩ := arithmetic_call false (boolList_extend wrep er) rrep
    N2 wroot nroot (by simp [N2,N1,H0,N0,twoCells,dense,Nat.add_assoc];omega)
    ⟨wroot,nroot,wroot,nroot⟩ 215 (frame::stack) source
  let H3 := H2++es
  let N3 := N2+es.length
  let e3 := threeCells N3
  obtain ⟨threeRun,threeRep⟩ := three_prefix H3 N3 sroot' nroot wroot sroot'
    (by simp [H3,H2,H1,H0,N3,N2,N1,N0,e2,twoCells,dense,Nat.add_assoc];omega) (frame::stack) source
  obtain ⟨eo,root,olen,orun,orep⟩ := arithmetic_call false (boolList_extend srep e3) threeRep
    (N3+4) wroot (N3+1) (by simp [H0,N3,N2,N1,N0,e3,twoCells,threeCells,dense,Nat.add_assoc];omega)
    ⟨sroot',N3+3,wroot,N3+1⟩ 221 (frame::stack) source
  have t200 : tickNatural program (state heap next a b c d (frame::stack) source 200)=
      some ⟨state heap next a b a d (frame::stack) source 201,[],0⟩ := by rfl
  have t201 : tickNatural program (state heap next a b a d (frame::stack) source 201)=
      some ⟨state heap next a b a d (⟨202,.r3,⟨a,b,a,d⟩⟩::frame::stack) source 162,[],0⟩ := by rfl
  have t202 : tickNatural program (state H0 N0 a b a sroot (frame::stack) source 202)=
      some ⟨state H0 N0 a b sroot sroot (frame::stack) source 203,[],0⟩ := by rfl
  have t208 : tickNatural program (state (H0++e2) (N0+5) (N0+4) b sroot (N0+3) (frame::stack) source 208)=
      some ⟨state (H0++e2) (N0+5) (N0+4) b sroot (N0+3)
        (⟨209,.r3,⟨N0+4,b,sroot,N0+3⟩⟩::frame::stack) source 110,[],0⟩ := by rfl
  have t209 : tickNatural program (state H1 N1 (N0+4) b sroot wroot (frame::stack) source 209)=
      some ⟨state H1 N1 (N0+4) sroot sroot wroot (frame::stack) source 210,[],0⟩ := by rfl
  have t210 : tickNatural program (state H1 N1 (N0+4) sroot sroot wroot (frame::stack) source 210)=
      some ⟨state H1 N1 (N0+4) sroot wroot wroot (frame::stack) source 211,[],0⟩ := by rfl
  have t211 : tickNatural program (state H1 N1 (N0+4) sroot wroot wroot (frame::stack) source 211)=
      some ⟨state H1 N1 (N0+4) sroot wroot wroot
        (⟨212,.r3,⟨N0+4,sroot,wroot,wroot⟩⟩::frame::stack) source 110,[],0⟩ := by rfl
  have t212 : tickNatural program (state H2 N2 (N0+4) sroot wroot nroot (frame::stack) source 212)=
      some ⟨state H2 N2 wroot sroot wroot nroot (frame::stack) source 213,[],0⟩ := by rfl
  have t213 : tickNatural program (state H2 N2 wroot sroot wroot nroot (frame::stack) source 213)=
      some ⟨state H2 N2 wroot nroot wroot nroot (frame::stack) source 214,[],0⟩ := by rfl
  have t214 : tickNatural program (state H2 N2 wroot nroot wroot nroot (frame::stack) source 214)=
      some ⟨state H2 N2 wroot nroot wroot nroot
        (⟨215,.r3,⟨wroot,nroot,wroot,nroot⟩⟩::frame::stack) source 114,[],0⟩ := by rfl
  have t215 : tickNatural program (state H3 N3 wroot nroot wroot sroot' (frame::stack) source 215)=
      some ⟨state H3 N3 sroot' nroot wroot sroot' (frame::stack) source 216,[],0⟩ := by rfl
  have t220 : tickNatural program (state (H3++e3) (N3+4) sroot' (N3+3) wroot (N3+1) (frame::stack) source 220)=
      some ⟨state (H3++e3) (N3+4) sroot' (N3+3) wroot (N3+1)
        (⟨221,.r3,⟨sroot',N3+3,wroot,N3+1⟩⟩::frame::stack) source 114,[],0⟩ := by rfl
  have t221 : tickNatural program (state ((H3++e3)++eo) (N3+4+eo.length) sroot' (N3+3) wroot root (frame::stack) source 221)=
      some ⟨state ((H3++e3)++eo) (N3+4+eo.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  refine ⟨en++e2++ew++er++es++e3++eo,root,?_,?_,?_⟩
  · simp [cells,nlen,wlen,rlen,slen,olen,e2,e3,twoCells,threeCells,Nat.add_assoc]
  · have all := NaturalRun.step t200 (NaturalRun.step t201 (run_append nrun (NaturalRun.step t202 (run_append twoRun (NaturalRun.step t208 (run_append wrun (NaturalRun.step t209 (NaturalRun.step t210 (NaturalRun.step t211 (run_append rrun (NaturalRun.step t212 (NaturalRun.step t213 (NaturalRun.step t214 (run_append srun (NaturalRun.step t215 (run_append threeRun (NaturalRun.step t220 (run_append orun (NaturalRun.step t221 (.done _))))))))))))))))))))
    convert all using 1 <;> simp [steps,state,H3,H2,H1,H0,N3,N2,N1,N0,e2,e3,twoCells,threeCells,List.append_assoc,Nat.add_assoc] <;> omega
  · simpa [BinaryFractionalGuesses.gridFuel,H3,H2,H1,H0,List.append_assoc] using orep
end DirectedFlowCutGap.GridFuelProgram
