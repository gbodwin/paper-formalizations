import DirectedFlowCutGap.MinimumGuessTrace

namespace DirectedFlowCutGap.MinimumGuess
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem compute {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c d : ℕ} {exponent : Bits}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (exp : BoolList heap b exponent)
    (graph : GraphAdjacencyProgram.Matrix heap c (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap d xs)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 10000)) (source : Bits) :
    ∃ k ext root,k ≤ inputSteps ds.length costs.toList exponent ∧
      NaturalRun program k (state heap next a b c d stack source 9998) []
        (state (heap++ext) (next+ext.length) a b c root stack source 9999) ∧
      Result (heap++ext) root (result adjacency ds costs exponent) := by
  obtain ⟨k,ext,root,bound,body,rep⟩ := guess_return adjacency costs encoded table exp graph pairs
    next dense ⟨a,b,c,d⟩ 9999 stack source
  have first : tickNatural program (state heap next a b c d stack source 9998)=
      some ⟨state heap next a b c d (⟨9999,.r3,⟨a,b,c,d⟩⟩::stack) source 9984,[],0⟩ := by rfl
  exact ⟨k+1,ext,root,bound,by simpa [Nat.add_comm] using NaturalRun.step first body,rep⟩
end DirectedFlowCutGap.MinimumGuess
