import DirectedFlowCutGap.MinimumGuessExecution

namespace DirectedFlowCutGap.MinimumGuess
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

theorem guess_bit {n H B : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (exponent : Bits)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    (initial : BitState 10000) (bounded : initial.Bounded H B) (pc0 : initial.pc=9998)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a
      (IndexedRationalRead.fields costs.toList))
    (exp : BoolList (eraseState initial).heap (eraseState initial).registers.b exponent)
    (graph : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.c
      (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList (eraseState initial).heap (eraseState initial).registers.d xs) :
    ∃ k charge out,Run program k charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d (result adjacency ds costs exponent) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a
        (IndexedRationalRead.fields costs.toList) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b exponent ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState initial).registers.c
        (GraphRelaxationRefinement.matrix adjacency) ∧
      DemandCollection.DemandList (eraseState out).heap (eraseState initial).registers.d xs ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=9999 ∧
      value out.next=out.heap.length ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 10000 H B
        (inputSteps ds.length costs.toList exponent) := by
  have nd : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have shape : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b
      (eraseState initial).registers.c (eraseState initial).registers.d [] initial.source 9998=eraseState initial := by
    cases initial with
    | mk heap next regs stack pc source =>
      cases regs
      simp_all [state,eraseState,State.map]
  obtain ⟨k,ext,root,bound,high,rep⟩ := compute adjacency costs encoded table exp graph pairs
    (eraseState initial).next nd [] initial.source
  rw [shape] at high
  have halt : tickNatural program
      (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
        (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
        root [] initial.source 9999)=none := by rfl
  obtain ⟨charge,out,run,erase,stop,cost,src⟩ := terminating_simulation bounded high halt
  refine ⟨k,charge,out,run,?_,?_,?_,?_,?_,src,?_,?_,?_,⟨ext,congrArg State.heap erase⟩,stop,
    cost.trans (SupportSearchEncoding.complete_mono 10000 H B _ _ bound)⟩
  · rw [erase];exact rep
  · rw [erase];exact BinaryIndexedPairRead.table_extend table ext
  · rw [erase];exact PackedBooleanConstructor.boolList_extend exp ext
  · rw [erase];exact GraphAdjacencyProgram.matrix_extend graph ext
  · rw [erase];exact DemandCollection.demands_extend pairs ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · exact congrArg State.pc erase
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];simp [state,nd]
    simpa [eraseState,State.map] using h
end DirectedFlowCutGap.MinimumGuess
