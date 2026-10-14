import DirectedFlowCutGap.FinalDispatchTail

namespace DirectedFlowCutGap.FinalDispatch
set_option maxRecDepth 32768
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

/-- Literal original-root dispatch, optional minimum and full family composition
on one append-only heap. No branch result or child output is supplied. -/
theorem compute {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c d : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap c xs)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 13320)) (source : Bits) :
    ∃ k ext root,k ≤ inputSteps adjacency costs ds ∧
      NaturalRun program k (state heap next a b c d stack source 13318) []
        (state (heap++ext) (next+ext.length) a b c root stack source 13319) ∧
      Output (heap++ext) root (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 := by
  let saved : Registers ℕ := ⟨a,b,c,d⟩
  let outer : Frame ℕ 13320 := ⟨13319,.r3,saved⟩
  have t0 : tickNatural program (state heap next a b c d stack source 13318)=
      some ⟨state heap next a b c d (outer::stack) source 13300,[],0⟩ := by
    simp [tickNatural,program,state,outer,saved]
  have t1 : tickNatural program (state heap next a b c d (outer::stack) source 13300)=
      some ⟨state heap next a b c d (⟨13301,.r3,saved⟩::outer::stack) source 13270,[],0⟩ := by
    simp [tickNatural,program,state,saved]
  obtain ⟨kp,ep,pr,bp,prefixRun,dispatch⟩ := prepare_dispatch adjacency costs encoded table graph pairs
    next dense saved 13301 (outer::stack) source
  obtain ⟨kt,et,root,bt,tailRun,output⟩ := continue_return adjacency costs encoded
    (BinaryIndexedPairRead.table_extend table ep) (GraphAdjacencyProgram.matrix_extend graph ep)
    (DemandCollection.demands_extend pairs ep) dispatch (next+ep.length) (by simp [dense])
    saved 13319 stack source
  refine ⟨kp+kt+2,ep++et,root,?_,?_,?_⟩
  · unfold inputSteps
    omega
  · have whole := NaturalRun.step t0 (.step t1 (run_append prefixRun tailRun))
    convert whole using 1 <;> simp [state,saved,List.append_assoc,Nat.add_assoc]
  · rw [BinaryFractionalGuesses.solveInput_value]
    simpa only [BinaryFractionalGuesses.solveSizedInput,List.append_assoc] using output
end DirectedFlowCutGap.FinalDispatch
