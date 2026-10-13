import DirectedFlowCutGap.LambdaRowPrefix

namespace DirectedFlowCutGap.LambdaRowProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem lambda_return {heap : NaturalHeap} {rows : List Fraction} {index dimension exponent : Bits}
    {a b c d : ℕ} (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (dim : BoolList heap c dimension) (exp : BoolList heap d exponent)
    (valid : value index<rows.length) (next : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 480) (stack : List (Frame ℕ 480)) (source : Bits) :
    ∃ ext root,ext.length=cells rows index dimension exponent ∧
      NaturalRun program (steps rows index dimension exponent)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 462) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (result rows index dimension exponent) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  obtain ⟨er,rr,lr,readRun,rep⟩ := row_prefix table idx valid next c d dense frames source
  let h0 := heap++er
  let n0 := next+er.length
  have nd : n0=h0.length := by simp [n0,h0,dense]
  have t0 : tickNatural program (state h0 n0 rr c d rr frames source 472)=
      some ⟨state h0 n0 rr c d rr (⟨473,.r3,⟨rr,c,d,rr⟩⟩::frames) source 460,[],0⟩ := by rfl
  obtain ⟨ec,root,lc,core,crep⟩ := core_call rep (boolList_extend dim er) (boolList_extend exp er)
    n0 rr nd ⟨rr,c,d,rr⟩ 473 frames source
  have t1 : tickNatural program (state (h0++ec) (n0+ec.length) rr c d root frames source 473)=
      some ⟨state (h0++ec) (n0+ec.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨er++ec,root,by simp [cells,lr,lc,Nat.add_assoc],?_,?_⟩
  · have whole := run_append readRun (.step t0 (run_append core (.step t1 (.done _))))
    convert whole using 1 <;> simp [steps,h0,n0,state,List.append_assoc,Nat.add_assoc]
    omega
  · simpa [result,h0,List.append_assoc] using crep
end DirectedFlowCutGap.LambdaRowProgram
