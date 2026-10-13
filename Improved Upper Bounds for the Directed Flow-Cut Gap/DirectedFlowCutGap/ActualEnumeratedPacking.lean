import DirectedFlowCutGap.EnumeratedPackingExecution

namespace DirectedFlowCutGap.EnumeratedPacking
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open CanonicalRationalSum (StoredList)

/-- The actual machine generates every vertex label from the capacity row, then
allocates metadata, derives parameters, initializes and iterates the full state. -/
theorem solve_rows_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    (initial : BitState 8420) (bounded : initial.Bounded H A) (pc0 : initial.pc=8410)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (capRep : StoredList (eraseState initial).heap (eraseState initial).registers.a capacity.toList)
    (graph : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.c
      (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList (eraseState initial).heap (eraseState initial).registers.d xs)
    (B : ℕ)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) :
    ∃ k charge out, Run program k charge initial [] out ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState out).registers.d RowVertices.vertexLabel
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a capacity.toList ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=8412 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 8420 H A (instructionBound ds.length n B) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d [] initial.source 8410=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨k,ext,vertexRoot,root,high,rep,bound⟩ := solve_rows adjacency capacity hn encoded
    capRep graph pairs (eraseState initial).next (eraseState initial).registers.b dense' initial.source B caps
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      vertexRoot (eraseState initial).registers.c root [] initial.source 8412)=none := by
    simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨k,charge,out,run,?_,?_,sourceOut,?_,?_,⟨ext,?_⟩,stop,
    (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 8420 H A _ _ bound)⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact CanonicalRationalSum.list_extend capRep ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=8412 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.EnumeratedPacking
