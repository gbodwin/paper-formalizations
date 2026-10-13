import DirectedFlowCutGap.LambdaCoreCalls

namespace DirectedFlowCutGap.LambdaCoreProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem dimension_prefix {heap : NaturalHeap} {dimension : Bits} {a b : ℕ}
    (dim : BoolList heap b dimension) (next c d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 432)) (source : Bits) :
    ∃ ext root,ext.length=6 ∧
      NaturalRun program 14 (state heap next a b c d stack source 400) []
        (state (heap++ext) (next+ext.length) a root (next+1) root stack source 407) ∧
      Stored (heap++ext) root (BinaryFractionalCore.naturalFraction dimension) ∧
      (heap++ext)[next]?=some (.pair a b) ∧
      (heap++ext)[next+1]?=some (.pair c next) := by
  let e0 : NaturalHeap := [.pair a b,.pair c next]
  let h0 := heap++e0
  let n0 := next+2
  have nd : n0=h0.length := by simp [n0,h0,e0,dense]
  have t0 : tickNatural program (state heap next a b c d stack source 400)=
      some ⟨state (heap++[.pair a b]) (next+1) a b c next stack source 401,[],0⟩ := by rfl
  have t1 : tickNatural program (state (heap++[.pair a b]) (next+1) a b c next stack source 401)=
      some ⟨state h0 n0 a b (next+1) next stack source 402,[],0⟩ := by
    simp [tickNatural,program,state,h0,n0,e0,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,Nat.add_assoc]
  have t2 : tickNatural program (state h0 n0 a b (next+1) next stack source 402)=
      some ⟨state h0 n0 b b (next+1) next stack source 403,[],0⟩ := by rfl
  have t3 : tickNatural program (state h0 n0 b b (next+1) next stack source 403)=
      some ⟨state h0 n0 b b (next+1) next
        (⟨404,.r3,⟨b,b,next+1,next⟩⟩::stack) source 6,[],0⟩ := by rfl
  obtain ⟨en,nr,len,nrun,nrep⟩ := natural_call (boolList_extend dim e0)
    n0 b (next+1) next nd ⟨b,b,next+1,next⟩ 404 stack source
  let H := h0++en
  let N := n0+en.length
  have pair0 : H[next]?=some (.pair a b) := by
    apply lookup_extend (k:=en)
    simp [h0,e0,dense]
  have pair1 : H[next+1]?=some (.pair c next) := by
    apply lookup_extend (k:=en)
    simp [h0,e0,dense]
  have t4 : tickNatural program (state H N b b (next+1) nr stack source 404)=
      some ⟨state H N b nr (next+1) nr stack source 405,[],0⟩ := by rfl
  have t5 : tickNatural program (state H N b nr (next+1) nr stack source 405)=
      some ⟨state H N next nr (next+1) nr stack source 406,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair1]
  have t6 : tickNatural program (state H N next nr (next+1) nr stack source 406)=
      some ⟨state H N a nr (next+1) nr stack source 407,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair0]
  refine ⟨e0++en,nr,by simp [e0,len],?_,?_,?_,?_⟩
  · have whole := NaturalRun.step t0 (.step t1 (.step t2 (.step t3
      (run_append nrun (.step t4 (.step t5 (.step t6 (.done _))))))))
    simpa [H,N,h0,n0,e0,state,len,List.append_assoc,Nat.add_assoc] using whole
  · simpa [h0,List.append_assoc] using nrep
  · simpa [H,h0,List.append_assoc] using pair0
  · simpa [H,h0,List.append_assoc] using pair1
end DirectedFlowCutGap.LambdaCoreProgram
