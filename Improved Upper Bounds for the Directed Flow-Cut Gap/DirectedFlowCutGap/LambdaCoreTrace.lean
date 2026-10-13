import DirectedFlowCutGap.LambdaCorePowerPrefix

namespace DirectedFlowCutGap.LambdaCoreProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem lambda_return {heap : NaturalHeap} {x : Fraction} {dimension exponent : Bits}
    {a b c : ℕ} (cost : Stored heap a x) (dim : BoolList heap b dimension)
    (exp : BoolList heap c exponent) (next d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 432) (stack : List (Frame ℕ 432)) (source : Bits) :
    ∃ ext root,ext.length=cells x dimension exponent ∧
      NaturalRun program (steps x dimension exponent)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 400) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (result x dimension exponent) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  obtain ⟨e0,dr,l0,prefixRun,dimrep,_,ctx⟩ := dimension_prefix (a:=a) dim next c d dense frames source
  let h0 := heap++e0
  let n0 := next+e0.length
  have nd0 : n0=h0.length := by simp [n0,h0,dense]
  have t0 : tickNatural program (state h0 n0 a dr (next+1) dr frames source 407)=
      some ⟨state h0 n0 a dr (next+1) dr
        (⟨408,.r3,⟨a,dr,next+1,dr⟩⟩::frames) source 169,[],0⟩ := by rfl
  obtain ⟨eq,qr,lq,qrun,qrep⟩ := quotient_call x (BinaryFractionalCore.naturalFraction dimension)
    (stored_extend cost e0) dimrep n0 (next+1) dr nd0 ⟨a,dr,next+1,dr⟩ 408 frames source
  let h1 := h0++eq
  let n1 := n0+eq.length
  have nd1 : n1=h1.length := by simp [n1,h1,nd0]
  have ctx1 : h1[next+1]?=some (.pair c next) := lookup_extend ctx eq
  have exp1 : BoolList h1 c exponent := boolList_extend (boolList_extend exp e0) eq
  obtain ⟨ep,pr,lp,prun,left,right⟩ := power_prefix ctx1 exp1 qrep n1 a dr nd1 frames source
  let h2 := h1++ep
  let n2 := n1+ep.length
  have nd2 : n2=h2.length := by simp [n2,h2,nd1]
  have t1 : tickNatural program (state h2 n2 qr pr n1 pr frames source 416)=
      some ⟨state h2 n2 qr pr n1 pr (⟨417,.r3,⟨qr,pr,n1,pr⟩⟩::frames) source 398,[],0⟩ := by rfl
  obtain ⟨em,mr,lm,mrun,mrep⟩ := product_call (quotient x dimension)
    (BinaryFractionalCore.naturalFraction (power exponent)) left right n2 n1 pr nd2
    ⟨qr,pr,n1,pr⟩ 417 frames source
  have t2 : tickNatural program (state (h2++em) (n2+em.length) qr pr n1 mr frames source 417)=
      some ⟨state (h2++em) (n2+em.length) saved.a saved.b saved.c mr stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨e0++eq++ep++em,mr,?_,?_,?_⟩
  · simp [cells,l0,lq,lp,lm,quotient,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega
  · have whole := run_append prefixRun (.step t0 (run_append qrun
      (run_append prun (.step t1 (run_append mrun (.step t2 (.done _)))))))
    convert whole using 1 <;> simp [steps,quotient,h2,n2,h1,n1,h0,n0,state,List.append_assoc,Nat.add_assoc]
    omega
  · simpa [result,h2,h1,h0,List.append_assoc] using mrep
end DirectedFlowCutGap.LambdaCoreProgram
