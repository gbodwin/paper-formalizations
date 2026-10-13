import DirectedFlowCutGap.GridFamilyInputCalls

namespace DirectedFlowCutGap.GridFamilyInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
set_option maxRecDepth 32768

theorem prepare_context {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) {xs : List DemandCollection.Demand}
    {heap : NaturalHeap} {a b c d : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap c xs)
    (metadata : GridInputProgram.Prepared heap d costs.toList)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 10760)) (source : Bits) :
    ∃ fr,NaturalRun program 4 (state heap next a b c d stack source 10731) []
      (state (heap++[.pair b c,.pair a next,.nil]) (next+3) (next+1) (next+2) fr d stack source 10735) ∧
      GridFamily.Context (heap++[.pair b c,.pair a next,.nil]) (next+1) adjacency costs xs ∧
      BoolList (heap++[.pair b c,.pair a next,.nil]) (next+2) [] ∧
      BoolList (heap++[.pair b c,.pair a next,.nil]) fr (fuel costs.toList) := by
  obtain ⟨pair,dim,wid,fr,hp,_hq,_hd,_hw,hf⟩ := metadata
  have t0 : tickNatural program (state heap next a b c d stack source 10731)=
      some ⟨state (heap++[.pair b c]) (next+1) a next c d stack source 10732,[],0⟩ := by rfl
  have t1 : tickNatural program (state (heap++[.pair b c]) (next+1) a next c d stack source 10732)=
      some ⟨state (heap++[.pair b c,.pair a next]) (next+2) (next+1) next c d stack source 10733,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,List.append_assoc,Nat.add_assoc]
  have look := lookup_extend hp [.pair b c,.pair a next]
  have t2 : tickNatural program (state (heap++[.pair b c,.pair a next]) (next+2) (next+1) next c d stack source 10733)=
      some ⟨state (heap++[.pair b c,.pair a next]) (next+2) (next+1) next fr d stack source 10734,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,look]
  have t3 : tickNatural program (state (heap++[.pair b c,.pair a next]) (next+2) (next+1) next fr d stack source 10734)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil]) (next+3) (next+1) (next+2) fr d stack source 10735,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,List.append_assoc,Nat.add_assoc]
  refine ⟨fr,?_,?_,?_,?_⟩
  · exact .step t0 (.step t1 (.step t2 (.step t3 (.done _))))
  · exact .intro (costRoot:=a) (graphRoot:=b) (demandsRoot:=c) (tail:=next)
      (by simp [dense]) (by simp [dense]) (BinaryIndexedPairRead.table_extend table _)
      (GraphAdjacencyProgram.matrix_extend graph _) (DemandCollection.demands_extend pairs _)
  · exact .nil (by simp [dense])
  · exact boolList_extend hf _
end DirectedFlowCutGap.GridFamilyInput
