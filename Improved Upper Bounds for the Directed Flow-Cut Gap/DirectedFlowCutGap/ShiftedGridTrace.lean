import DirectedFlowCutGap.ShiftedGridCalls

namespace DirectedFlowCutGap.ShiftedGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram CanonicalRationalSum

theorem shifted_return {heap : NaturalHeap} {rows : List Fraction} {index exponent : Bits}
    {a b c : ℕ} (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (exp : BoolList heap c exponent)
    (valid : value index<rows.length) (next d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 1220) (stack : List (Frame ℕ 1220)) (source : Bits) :
    ∃ ext root,ext.length=cells rows index exponent ∧
      NaturalRun program (steps rows index exponent)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1200) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (result rows index exponent) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 1200)=
      some ⟨state heap next a b c d (⟨1201,.r3,⟨a,b,c,d⟩⟩::frames) source 1038,[],0⟩ := by rfl
  obtain ⟨el,lr,ll,lambdaRun,sc⟩ := grid_call table idx exp valid next d dense
    ⟨a,b,c,d⟩ 1201 frames source
  let h1 := heap++el
  let n1 := next+el.length
  have nd : n1=h1.length := by simp [n1,h1,dense]
  have t1 : tickNatural program (state h1 n1 a b c lr frames source 1201)=
      some ⟨state h1 n1 a lr c lr frames source 1202,[],0⟩ := by rfl
  have t2 : tickNatural program (state h1 n1 a lr c lr frames source 1202)=
      some ⟨state h1 n1 a lr c lr (⟨1203,.r3,⟨a,lr,c,lr⟩⟩::frames) source 1198,[],0⟩ := by rfl
  obtain ⟨er,root,le,rowRun,rep⟩ := row_call
    (list_extend (ScalarAdditionRow.stored_of_table table) el) sc n1 c lr nd
    ⟨a,lr,c,lr⟩ 1203 frames source
  have t3 : tickNatural program (state (h1++er) (n1+er.length) a lr c root frames source 1203)=
      some ⟨state (h1++er) (n1+er.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨el++er,root,?_,?_,?_⟩
  · simp only [cells,List.length_append,ll,le]
  · have whole := NaturalRun.step t0 (run_append lambdaRun (.step t1 (.step t2
      (run_append rowRun (.step t3 (.done _))))))
    convert whole using 1 <;> simp [steps,h1,n1,state,List.append_assoc,Nat.add_assoc]
    omega
  · simpa [result,h1,List.append_assoc] using rep
end DirectedFlowCutGap.ShiftedGridProgram
