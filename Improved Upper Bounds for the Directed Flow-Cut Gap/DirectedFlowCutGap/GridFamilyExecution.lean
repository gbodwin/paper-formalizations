import DirectedFlowCutGap.GridFamilyTrace

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem compute {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c : ℕ} {exponent fuel : Bits}
    (context : Context heap a adjacency costs xs) (exp : BoolList heap b exponent)
    (input : BoolList heap c fuel) (next d : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ k ext root,k ≤ instructionBound ds.length costs.toList exponent fuel+1 ∧
      NaturalRun program k (state heap next a b c d [] source 10178) []
        (state (heap++ext) (next+ext.length) a b c root [] source 10179) ∧
      StateList (heap++ext) root (values adjacency ds costs exponent fuel) := by
  have first : tickNatural program (state heap next a b c d [] source 10178)=
      some ⟨state heap next a b c d [⟨10179,.r3,⟨a,b,c,d⟩⟩] source 10130,[],0⟩ := by rfl
  obtain ⟨k,ext,root,bound,run,rep⟩ := loop_return adjacency costs encoded context exp input next d dense
    ⟨a,b,c,d⟩ .r3 10179 [] source
  refine ⟨k+1,ext,root,by omega,?_,rep⟩
  simpa [state,Registers.set] using NaturalRun.step first run
end DirectedFlowCutGap.GridFamily
