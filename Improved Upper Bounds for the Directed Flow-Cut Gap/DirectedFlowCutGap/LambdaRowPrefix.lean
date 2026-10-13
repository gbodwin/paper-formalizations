import DirectedFlowCutGap.LambdaRowCalls

namespace DirectedFlowCutGap.LambdaRowProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem row_prefix {heap : NaturalHeap} {rows : List Fraction} {index : Bits} {a b : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (valid : value index<rows.length)
    (next c d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 480)) (source : Bits) :
    ∃ ext root,ext.length=value index+4 ∧
      NaturalRun program (BinaryIndexedPairRead.steps index+14)
        (state heap next a b c d stack source 462) []
        (state (heap++ext) (next+ext.length) root c d root stack source 472) ∧
      Stored (heap++ext) root (IndexedRationalRead.lookup rows index) := by
  let e0 : NaturalHeap := [.pair a d,.pair c next]
  let h0 := heap++e0
  let n0 := next+2
  have nd : n0=h0.length := by simp [n0,h0,e0,dense]
  have pair0 : h0[next]?=some (.pair a d) := by simp [h0,e0,dense]
  have pair1 : h0[next+1]?=some (.pair c next) := by simp [h0,e0,dense]
  have t0 : tickNatural program (state heap next a b c d stack source 462)=
      some ⟨state (heap++[.pair a d]) (next+1) a b c next stack source 463,[],0⟩ := by rfl
  have t1 : tickNatural program (state (heap++[.pair a d]) (next+1) a b c next stack source 463)=
      some ⟨state h0 n0 a b (next+1) next stack source 464,[],0⟩ := by
    simp [tickNatural,program,state,h0,n0,e0,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,Nat.add_assoc]
  have t2 : tickNatural program (state h0 n0 a b (next+1) next stack source 464)=
      some ⟨state h0 n0 b b (next+1) next stack source 465,[],0⟩ := by rfl
  have t3 : tickNatural program (state h0 n0 b b (next+1) next stack source 465)=
      some ⟨state h0 n0 b next (next+1) next stack source 466,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair1]
  have t4 : tickNatural program (state h0 n0 b next (next+1) next stack source 466)=
      some ⟨state h0 n0 b a (next+1) next stack source 467,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair0]
  have t5 : tickNatural program (state h0 n0 b a (next+1) next stack source 467)=
      some ⟨state h0 n0 b a (next+1) next (⟨468,.r3,⟨b,a,next+1,next⟩⟩::stack) source 28,[],0⟩ := by rfl
  obtain ⟨er,root,len,readRun,rep⟩ := read_call (boolList_extend idx e0)
    (BinaryIndexedPairRead.table_extend table e0) valid n0 (next+1) next nd ⟨b,a,next+1,next⟩ 468 stack source
  let H := h0++er
  let N := n0+er.length
  have p0 : H[next]?=some (.pair a d) := lookup_extend pair0 er
  have p1 : H[next+1]?=some (.pair c next) := lookup_extend pair1 er
  have t6 : tickNatural program (state H N b a (next+1) root stack source 468)=
      some ⟨state H N root a (next+1) root stack source 469,[],0⟩ := by rfl
  have t7 : tickNatural program (state H N root a (next+1) root stack source 469)=
      some ⟨state H N root c (next+1) root stack source 470,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,p1]
  have t8 : tickNatural program (state H N root c (next+1) root stack source 470)=
      some ⟨state H N root c next root stack source 471,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,p1]
  have t9 : tickNatural program (state H N root c next root stack source 471)=
      some ⟨state H N root c d root stack source 472,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,p0]
  refine ⟨e0++er,root,by simp only [e0,List.length_append,List.length_cons,List.length_nil,len];omega,?_,?_⟩
  · have whole := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5
      (run_append readRun (.step t6 (.step t7 (.step t8 (.step t9 (.done _)))))))))))
    convert whole using 1 <;> simp [H,N,h0,n0,e0,state,len,List.append_assoc,Nat.add_assoc]
    omega
  · simpa [h0,List.append_assoc] using rep
end DirectedFlowCutGap.LambdaRowProgram
