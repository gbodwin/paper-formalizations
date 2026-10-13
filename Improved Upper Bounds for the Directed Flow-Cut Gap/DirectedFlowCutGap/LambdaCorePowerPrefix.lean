import DirectedFlowCutGap.LambdaCorePrefix

namespace DirectedFlowCutGap.LambdaCoreProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem power_prefix {heap : NaturalHeap} {exponent : Bits} {q : Fraction}
    {c d exp old : ℕ} (context : heap[c]?=some (.pair exp old))
    (powerInput : BoolList heap exp exponent) (left : Stored heap d q)
    (next a b : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 432)) (source : Bits) :
    ∃ ext root,ext.length=BinaryPowerProgram.cells exponent+5 ∧
      NaturalRun program (BinaryPowerProgram.steps exponent+17)
        (state heap next a b c d stack source 408) []
        (state (heap++ext) (next+ext.length) d root next root stack source 416) ∧
      Stored (heap++ext) d q ∧
      Stored (heap++ext) root (BinaryFractionalCore.naturalFraction (power exponent)) := by
  let e0 : NaturalHeap := [.pair d c]
  let h0 := heap++e0
  let n0 := next+1
  have nd0 : n0=h0.length := by simp [n0,h0,e0,dense]
  have savedPair : h0[next]?=some (.pair d c) := by simp [h0,e0,dense]
  have oldPair : h0[c]?=some (.pair exp old) := lookup_extend context e0
  have t0 : tickNatural program (state heap next a b c d stack source 408)=
      some ⟨state h0 n0 a b next d stack source 409,[],0⟩ := by rfl
  have t1 : tickNatural program (state h0 n0 a b next d stack source 409)=
      some ⟨state h0 n0 c b next d stack source 410,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,savedPair]
  have t2 : tickNatural program (state h0 n0 c b next d stack source 410)=
      some ⟨state h0 n0 exp b next d stack source 411,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,oldPair]
  have t3 : tickNatural program (state h0 n0 exp b next d stack source 411)=
      some ⟨state h0 n0 exp b next d (⟨412,.r3,⟨exp,b,next,d⟩⟩::stack) source 266,[],0⟩ := by rfl
  obtain ⟨ep,pr,plen,prun,prep⟩ := power_call (boolList_extend powerInput e0)
    n0 b next d nd0 ⟨exp,b,next,d⟩ 412 stack source
  let h1 := h0++ep
  let n1 := n0+ep.length
  have nd1 : n1=h1.length := by simp [n1,h1,nd0]
  have t4 : tickNatural program (state h1 n1 exp b next pr stack source 412)=
      some ⟨state h1 n1 pr b next pr stack source 413,[],0⟩ := by rfl
  have t5 : tickNatural program (state h1 n1 pr b next pr stack source 413)=
      some ⟨state h1 n1 pr b next pr (⟨414,.r3,⟨pr,b,next,pr⟩⟩::stack) source 6,[],0⟩ := by rfl
  obtain ⟨en,nr,nlen,nrun,nrep⟩ := natural_call prep n1 b next pr nd1
    ⟨pr,b,next,pr⟩ 414 stack source
  let h2 := h1++en
  let n2 := n1+en.length
  have finalPair : h2[next]?=some (.pair d c) :=
    lookup_extend (lookup_extend savedPair ep) en
  have t6 : tickNatural program (state h2 n2 pr b next nr stack source 414)=
      some ⟨state h2 n2 pr nr next nr stack source 415,[],0⟩ := by rfl
  have t7 : tickNatural program (state h2 n2 pr nr next nr stack source 415)=
      some ⟨state h2 n2 d nr next nr stack source 416,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,finalPair]
  refine ⟨e0++ep++en,nr,by simp [e0,plen,nlen],?_,stored_extend left _,?_⟩
  · have whole := NaturalRun.step t0 (.step t1 (.step t2 (.step t3
      (run_append prun (.step t4 (.step t5 (run_append nrun (.step t6 (.step t7 (.done _))))))))))
    convert whole using 1 <;> simp [h2,n2,h1,n1,h0,n0,e0,state,List.append_assoc,Nat.add_assoc]
    all_goals omega
  · simpa [h1,h0,List.append_assoc] using nrep
end DirectedFlowCutGap.LambdaCoreProgram
