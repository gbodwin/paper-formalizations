import DirectedFlowCutGap.OriginalRowMinimumCalls

namespace DirectedFlowCutGap.OriginalRowMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor CanonicalRationalSum GraphDiscoveryProgram

theorem minimum_return {heap : NaturalHeap} {rows : List Fraction} {a : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 320) (stack : List (Frame ℕ 320)) (source : Bits) :
    ∃ k ext root,k+1≤ inputSteps rows ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 300) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PositiveMinimum.Result (heap++ext) root (result rows) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 300)=
      some ⟨state heap next a b c d (⟨301,.r3,⟨a,b,c,d⟩⟩::frames) source 40,[],0⟩ := by rfl
  obtain ⟨kv,ev,vr,bv,vertexRun,vertices⟩ := vertex_call (ScalarAdditionRow.stored_of_table table)
    next b c d dense ⟨a,b,c,d⟩ 301 frames source
  let h1 := heap++ev
  let n1 := next+ev.length
  have nd : n1=h1.length := by simp [n1,h1,dense]
  have t1 : tickNatural program (state h1 n1 a b c vr frames source 301)=
      some ⟨state h1 n1 a a c vr frames source 302,[],0⟩ := by rfl
  have t2 : tickNatural program (state h1 n1 a a c vr frames source 302)=
      some ⟨state h1 n1 vr a c vr frames source 303,[],0⟩ := by rfl
  have t3 : tickNatural program (state h1 n1 vr a c vr frames source 303)=
      some ⟨state h1 n1 vr a c vr (⟨304,.r3,⟨vr,a,c,vr⟩⟩::frames) source 298,[],0⟩ := by rfl
  obtain ⟨km,em,root,bm,minimumRun,rep⟩ := minimum_call vertices
    (BinaryIndexedPairRead.table_extend table ev) n1 c vr nd ⟨vr,a,c,vr⟩ 304 frames source
  have t4 : tickNatural program (state (h1++em) (n1+em.length) vr a c root frames source 304)=
      some ⟨state (h1++em) (n1+em.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨kv+km+5,ev++em,root,by unfold inputSteps;omega,?_,?_⟩
  · have whole := NaturalRun.step t0 (run_append vertexRun (.step t1 (.step t2 (.step t3
      (run_append minimumRun (.step t4 (.done _)))))))
    convert whole using 1 <;> simp [h1,n1,state,List.append_assoc,Nat.add_assoc]
  · simpa [h1,List.append_assoc] using rep
end DirectedFlowCutGap.OriginalRowMinimum
