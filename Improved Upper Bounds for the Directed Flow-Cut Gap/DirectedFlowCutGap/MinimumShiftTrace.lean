import DirectedFlowCutGap.MinimumShiftBound

namespace DirectedFlowCutGap.MinimumShift
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor CanonicalRationalSum

set_option maxRecDepth 16384 in
theorem shifted_return {n : ℕ} (costs : BinaryFractionalRows.Row n) {heap : NaturalHeap}
    {a c : ℕ} {exponent : Bits}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (exp : BoolList heap c exponent) (next b d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 1560) (stack : List (Frame ℕ 1560)) (source : Bits) :
    ∃ k ext root,k+1 ≤ inputSteps costs.toList exponent ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1540) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Result (heap++ext) root (result costs exponent) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 1540)=
      some ⟨state heap next a b c d (⟨1541,.r3,⟨a,b,c,d⟩⟩::frames) source 318,[],0⟩ := by rfl
  obtain ⟨km,em,mr,bm,mrun,mrep⟩ := minimum_call table next b c d dense ⟨a,b,c,d⟩ 1541 frames source
  let h1 := heap++em
  let n1 := next+em.length
  have nd : n1=h1.length := by simp [h1,n1,dense]
  cases hm : OriginalRowMinimum.result costs.toList with
  | none =>
    have nil : h1[mr]?=some .nil := by simpa [hm,PositiveMinimum.Result,h1] using mrep
    have t1 : tickNatural program (state h1 n1 a b c mr frames source 1541)=
        some ⟨state h1 n1 a b c mr frames source 1547,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,nil,tagBranch]
    have t2 : tickNatural program (state h1 n1 a b c mr frames source 1547)=
        some ⟨state h1 n1 saved.a saved.b saved.c mr stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨km+3,em,mr,by unfold inputSteps;omega,?_,?_⟩
    · have whole := NaturalRun.step t0 (run_append mrun (.step t1 (.step t2 (.done _))))
      simpa [h1,n1,state,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using whole
    · rw [result_selected,hm];exact nil
  | some x =>
    obtain ⟨valid,width⟩ := OriginalRowMinimum.selected_valid costs hm
    have valid' : value x.1<costs.toList.length := by simpa using valid
    have width' : x.1.length≤costs.toList.length := by simpa using width
    rw [hm] at mrep
    obtain ⟨item,⟨_root,cost,pair,_costRep⟩,_score,word⟩ := mrep
    have t1 : tickNatural program (state h1 n1 a b c mr frames source 1541)=
        some ⟨state h1 n1 a b c mr frames source 1542,[],0⟩ := by
      simp [tickNatural,program,state,h1,Registers.get,pair,tagBranch]
    have t2 : tickNatural program (state h1 n1 a b c mr frames source 1542)=
        some ⟨state h1 n1 a item.payload c mr frames source 1543,[],0⟩ := by
      simp [tickNatural,program,state,h1,pair,Registers.get,Registers.set]
    have t3 : tickNatural program (state h1 n1 a item.payload c mr frames source 1543)=
        some ⟨state h1 n1 a item.payload c mr (⟨1544,.r3,⟨a,item.payload,c,mr⟩⟩::frames) source 1538,[],0⟩ := by rfl
    obtain ⟨es,root,srun,rep⟩ := shift_call (BinaryIndexedPairRead.table_extend table em) word
      (boolList_extend exp em) valid' n1 mr nd ⟨a,item.payload,c,mr⟩ 1544 frames source
    have t4 : tickNatural program (state (h1++es) (n1+es.length) a item.payload c root frames source 1544)=
        some ⟨state (h1++es) (n1+es.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    have sb := (ShiftedGridProgram.steps_bound costs.toList x.1 exponent valid').trans
      (shift_envelope costs.toList x.1 exponent width')
    refine ⟨km+(ShiftedGridProgram.steps costs.toList x.1 exponent+2)+5,em++es,root,
      by unfold inputSteps;omega,?_,?_⟩
    · have whole := NaturalRun.step t0 (run_append mrun (.step t1 (.step t2 (.step t3
        (run_append srun (.step t4 (.done _)))))))
      convert whole using 1 <;> simp [h1,n1,state,List.append_assoc,Nat.add_assoc]
    · rw [result_selected,hm]
      simpa [Result,h1,List.append_assoc] using rep
end DirectedFlowCutGap.MinimumShift
