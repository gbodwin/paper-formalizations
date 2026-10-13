import DirectedFlowCutGap.LambdaGridCalls

namespace DirectedFlowCutGap.LambdaGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem lambda_return {heap : NaturalHeap} {rows : List Fraction} {index exponent : Bits}
    {a b c : ℕ} (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (exp : BoolList heap c exponent)
    (valid : value index<rows.length) (next d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 1040) (stack : List (Frame ℕ 1040)) (source : Bits) :
    ∃ ext root,ext.length=cells rows index exponent ∧
      NaturalRun program (steps rows index exponent)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1024) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (result rows index exponent) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 1024)=
      some ⟨state heap next a b c d (⟨1025,.r3,⟨a,b,c,d⟩⟩::frames) source 542,[],0⟩ := by rfl
  obtain ⟨eg,gr,lg,gridRun,prep⟩ := grid_call table next b c d dense ⟨a,b,c,d⟩ 1025 frames source
  obtain ⟨pair,dim,wid,fuel,hg,hp,hd,_,_⟩ := prep
  let h0 := heap++eg
  let n0 := next+eg.length
  let e1 : NaturalHeap := [.pair c gr]
  let h1 := h0++e1
  let n1 := n0+1
  have nd : n1=h1.length := by simp [n1,n0,h1,h0,e1,dense,Nat.add_assoc]
  have ctx : h1[n0]?=some (.pair c gr) := by simp [h1,e1,n0,h0,dense]
  have grid : h1[gr]?=some (.pair pair fuel) := lookup_extend hg e1
  have dims : h1[pair]?=some (.pair dim wid) := lookup_extend hp e1
  have t1 : tickNatural program (state h0 n0 a b c gr frames source 1025)=
      some ⟨state h1 n1 a b c n0 frames source 1026,[],0⟩ := by rfl
  have t2 : tickNatural program (state h1 n1 a b c n0 frames source 1026)=
      some ⟨state h1 n1 a b gr n0 frames source 1027,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ctx]
  have t3 : tickNatural program (state h1 n1 a b gr n0 frames source 1027)=
      some ⟨state h1 n1 a b pair n0 frames source 1028,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,grid]
  have t4 : tickNatural program (state h1 n1 a b pair n0 frames source 1028)=
      some ⟨state h1 n1 a b dim n0 frames source 1029,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,dims]
  have t5 : tickNatural program (state h1 n1 a b dim n0 frames source 1029)=
      some ⟨state h1 n1 a b dim c frames source 1030,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ctx]
  have t6 : tickNatural program (state h1 n1 a b dim c frames source 1030)=
      some ⟨state h1 n1 a b dim c (⟨1031,.r3,⟨a,b,dim,c⟩⟩::frames) source 1022,[],0⟩ := by rfl
  obtain ⟨er,root,lr,rowRun,rep⟩ := row_call
    (BinaryIndexedPairRead.table_extend (BinaryIndexedPairRead.table_extend table eg) e1)
    (boolList_extend (boolList_extend idx eg) e1) (boolList_extend hd e1)
    (boolList_extend (boolList_extend exp eg) e1) valid n1 nd ⟨a,b,dim,c⟩ 1031 frames source
  have t7 : tickNatural program (state (h1++er) (n1+er.length) a b dim root frames source 1031)=
      some ⟨state (h1++er) (n1+er.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨eg++e1++er,root,?_,?_,?_⟩
  · simp only [cells,e1,List.length_append,List.length_cons,List.length_nil,lg,lr]
    omega
  · have whole := NaturalRun.step t0 (run_append gridRun (.step t1 (.step t2 (.step t3 (.step t4
      (.step t5 (.step t6 (run_append rowRun (.step t7 (.done _))))))))))
    convert whole using 1 <;> simp [steps,h1,n1,h0,n0,e1,state,List.append_assoc,Nat.add_assoc]
    all_goals omega
  · simpa [result,h1,h0,List.append_assoc] using rep
end DirectedFlowCutGap.LambdaGridProgram
