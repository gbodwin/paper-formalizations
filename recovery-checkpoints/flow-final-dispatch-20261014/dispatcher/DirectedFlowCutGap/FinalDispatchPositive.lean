import DirectedFlowCutGap.FinalDispatchOutput

namespace DirectedFlowCutGap.FinalDispatch
set_option maxRecDepth 32768
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

/-- The literal optional-minimum scan selects the branch; the grid call still
receives the actual original roots, and its redundant minimum work is charged. -/
theorem positive_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c d : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap c xs)
    (next : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 13320)
    (stack : List (Frame ℕ 13320)) (source : Bits) :
    ∃ k ext root,k≤OriginalRowMinimum.inputSteps costs.toList+
        GridFamilyInput.inputSteps ds.length costs.toList+8 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 13307) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Output (heap++ext) root (positiveOutput adjacency costs ds) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 13307)=
      some ⟨state heap next a b c d (⟨13308,.r3,⟨a,b,c,d⟩⟩::frames) source 13262,[],0⟩ := by rfl
  obtain ⟨km,em,mr,bm,minimumRun,minimum⟩ := minimum_call table next b c d dense
    ⟨a,b,c,d⟩ 13308 frames source
  rw [OriginalRowMinimum.result_original] at minimum
  cases hm : (BinaryFractionalDispatch.minimumPositive costs).1 with
  | none =>
    have look : (heap++em)[mr]?=some .nil := by
      simpa only [hm,Option.map_none,PositiveMinimum.Result] using minimum
    have t1 : tickNatural program (state (heap++em) (next+em.length) a b c mr frames source 13308)=
        some ⟨state (heap++em) (next+em.length) a b c mr frames source 13305,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,look,tagBranch]
    have t2 : tickNatural program (state (heap++em) (next+em.length) a b c mr frames source 13305)=
        some ⟨state (heap++em) (next+em.length) saved.a saved.b saved.c mr stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨km+3,em,mr,by omega,?_,?_⟩
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        NaturalRun.step t0 (run_append minimumRun (.step t1 (.step t2 (.done _))))
    · simpa only [positiveOutput,hm,Output] using look
  | some j =>
    simp only [hm,Option.map_some,PositiveMinimum.Result] at minimum
    obtain ⟨item,⟨_address,cr,look,_stored⟩,_encoded⟩ := minimum
    have t1 : tickNatural program (state (heap++em) (next+em.length) a b c mr frames source 13308)=
        some ⟨state (heap++em) (next+em.length) a b c mr frames source 13309,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,look,tagBranch]
    have t2 : tickNatural program (state (heap++em) (next+em.length) a b c mr frames source 13309)=
        some ⟨state (heap++em) (next+em.length) a b c mr
          (⟨13310,.r3,⟨a,b,c,mr⟩⟩::frames) source 10758,[],0⟩ := by rfl
    obtain ⟨kg,eg,gr,bg,gridRun,grid⟩ := grid_call adjacency costs encoded
      (BinaryIndexedPairRead.table_extend table em) (GraphAdjacencyProgram.matrix_extend graph em)
      (DemandCollection.demands_extend pairs em) (next+em.length) (by simp [dense])
      ⟨a,b,c,mr⟩ 13310 frames source
    rw [GridFamilyInput.values_original adjacency ds costs j hm] at grid
    let h2 := heap++em++eg
    let n2 := next+em.length+eg.length
    let ep : NaturalHeap := [.nil,.pair n2 gr]
    have nd : n2=h2.length := by simp [n2,h2,dense]
    have t3 : tickNatural program (state h2 n2 a b c gr frames source 13310)=
        some ⟨state (h2++[.nil]) (n2+1) n2 b c gr frames source 13311,[],0⟩ := by rfl
    have t4 : tickNatural program (state (h2++[.nil]) (n2+1) n2 b c gr frames source 13311)=
        some ⟨state (h2++ep) (n2+2) n2 b c (n2+1) frames source 13305,[],0⟩ := by
      simp [tickNatural,program,state,ep,Registers.get,Registers.set,allocateNatural,Recipe.cell,
        List.append_assoc,Nat.add_assoc]
    have t5 : tickNatural program (state (h2++ep) (n2+2) n2 b c (n2+1) frames source 13305)=
        some ⟨state (h2++ep) (n2+2) saved.a saved.b saved.c (n2+1) stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨km+kg+6,em++eg++ep,n2+1,by omega,?_,?_⟩
    · have whole := NaturalRun.step t0 (run_append minimumRun (.step t1 (.step t2
        (run_append gridRun (.step t3 (.step t4 (.step t5 (.done _))))))))
      convert whole using 1 <;> simp [state,h2,n2,ep,List.append_assoc,Nat.add_assoc]
    · simp only [positiveOutput,hm,Output]
      refine ⟨n2,gr,?_,?_,?_⟩
      · change (h2++ep)[n2+1]?=some (.pair n2 gr)
        simp [ep,nd]
      · change (h2++ep)[n2]?=some .nil
        simp [ep,nd]
      · simpa only [h2,List.append_assoc] using GridFamily.list_extend grid ep
end DirectedFlowCutGap.FinalDispatch
