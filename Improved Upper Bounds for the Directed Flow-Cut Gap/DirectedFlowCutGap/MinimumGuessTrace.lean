import DirectedFlowCutGap.MinimumGuessPreparation

set_option maxRecDepth 32768

namespace DirectedFlowCutGap.MinimumGuess
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor CanonicalRationalSum

theorem guess_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c d : ℕ} {exponent : Bits}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (exp : BoolList heap b exponent)
    (graph : GraphAdjacencyProgram.Matrix heap c (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap d xs)
    (next : ℕ) (dense : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 10000) (stack : List (Frame ℕ 10000)) (source : Bits) :
    ∃ k ext root,k+1 ≤ inputSteps ds.length costs.toList exponent ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 9984) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Result (heap++ext) root (result adjacency ds costs exponent) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 9984)=
      some ⟨state heap next a b c d (⟨9985,.r1,⟨a,b,c,d⟩⟩::frames) source 9980,[],0⟩ := by rfl
  obtain ⟨km,em,mr,bm,mrun,mrep⟩ := prepare_return costs table exp next c d dense ⟨a,b,c,d⟩ 9985 frames source
  let h1 := heap++em
  let n1 := next+em.length
  have nd : n1=h1.length := by simp [h1,n1,dense]
  cases hm : (BinaryFractionalDispatch.minimumPositive costs).1 with
  | none =>
    have nil : h1[mr]?=some .nil := by
      simpa [MinimumShift.result_original,hm,MinimumShift.Result,h1] using mrep
    have t1 : tickNatural program (state h1 n1 a mr c d frames source 9985)=
        some ⟨state h1 n1 a mr c d frames source 9991,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,nil,tagBranch]
    have t2 : tickNatural program (state h1 n1 a mr c d frames source 9991)=
        some ⟨state h1 n1 a mr c mr frames source 9992,[],0⟩ := by rfl
    have t3 : tickNatural program (state h1 n1 a mr c mr frames source 9992)=
        some ⟨state h1 n1 saved.a saved.b saved.c mr stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨km+4,em,mr,by unfold inputSteps;omega,?_,?_⟩
    · have whole := NaturalRun.step t0 (run_append mrun (.step t1 (.step t2 (.step t3 (.done _)))))
      simpa [h1,n1,state,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using whole
    · simpa [result,hm,Result,h1] using nil
  | some i =>
    have caps : StoredList h1 mr (shifted costs i exponent).toList := by
      simpa [MinimumShift.result_original,hm,MinimumShift.Result,h1,shifted] using mrep
    have pair : ∃ head tail,h1[mr]?=some (.pair head tail) := by
      cases hv : (shifted costs i exponent).toList with
      | nil =>
        have len := (shifted costs i exponent).length_toList
        rw [hv] at len
        have hi := i.isLt
        simp only [List.length_nil] at len
        omega
      | cons x rest =>
        rw [hv] at caps
        cases caps with
        | cons hp _ _ => exact ⟨_,_,hp⟩
    obtain ⟨head,tail,hp⟩ := pair
    have t1 : tickNatural program (state h1 n1 a mr c d frames source 9985)=
        some ⟨state h1 n1 a mr c d frames source 9986,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t2 : tickNatural program (state h1 n1 a mr c d frames source 9986)=
        some ⟨state h1 n1 mr mr c d frames source 9987,[],0⟩ := by rfl
    have t3 : tickNatural program (state h1 n1 mr mr c d frames source 9987)=
        some ⟨state h1 n1 mr mr c d (⟨9988,.r3,⟨mr,mr,c,d⟩⟩::frames) source 9970,[],0⟩ := by rfl
    obtain ⟨ks,es,root,bs,srun,rep⟩ := solve_call adjacency costs i exponent encoded caps
      (GraphAdjacencyProgram.matrix_extend graph em) (DemandCollection.demands_extend pairs em)
      n1 mr nd ⟨mr,mr,c,d⟩ 9988 frames source
    have t4 : tickNatural program (state (h1++es) (n1+es.length) mr mr c root frames source 9988)=
        some ⟨state (h1++es) (n1+es.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨km+ks+5,em++es,root,?_,?_,?_⟩
    · unfold inputSteps
      simp only [costs.length_toList]
      omega
    · have whole := NaturalRun.step t0 (run_append mrun (.step t1 (.step t2 (.step t3
        (run_append srun (.step t4 (.done _)))))))
      convert whole using 1 <;> simp [h1,n1,state,List.append_assoc,Nat.add_assoc]
    · simpa [result,hm,Result,h1,List.append_assoc] using rep
end DirectedFlowCutGap.MinimumGuess
