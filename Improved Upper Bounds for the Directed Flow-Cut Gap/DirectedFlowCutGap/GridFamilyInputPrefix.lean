import DirectedFlowCutGap.GridFamilyInputPrepare
namespace DirectedFlowCutGap.GridFamilyInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
set_option maxRecDepth 32768

theorem prepare_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) {xs : List DemandCollection.Demand}
    {heap : NaturalHeap} {a b c d : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap c xs)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 10760)) (source : Bits) :
    ∃ ext cp xp fp gp,NaturalRun program (GridInputProgram.steps costs.toList+7)
      (state heap next a b c d stack source 10730) []
      (state (heap++ext) (next+ext.length) cp xp fp gp stack source 10735) ∧
      GridFamily.Context (heap++ext) cp adjacency costs xs ∧
      BoolList (heap++ext) xp [] ∧ BoolList (heap++ext) fp (fuel costs.toList) := by
  let saved : Registers ℕ := ⟨a,b,c,d⟩
  have t0 : tickNatural program (state heap next a b c d stack source 10730)=
      some ⟨state heap next a b c d (⟨10731,.r3,saved⟩::stack) source 10722,[],0⟩ := by rfl
  obtain ⟨eg,gridRoot,grid,metadata⟩ := grid_call table next b c d dense saved 10731 stack source
  have nd : next+eg.length=(heap++eg).length := by simp [dense]
  obtain ⟨fr,prep,context,exp,input⟩ := prepare_context adjacency costs
    (BinaryIndexedPairRead.table_extend table eg) (GraphAdjacencyProgram.matrix_extend graph eg)
    (DemandCollection.demands_extend pairs eg) metadata (next+eg.length) nd stack source
  let ep : NaturalHeap := [.pair b c,.pair a (next+eg.length),.nil]
  refine ⟨eg++ep,next+eg.length+1,next+eg.length+2,fr,gridRoot,?_,?_,?_,?_⟩
  · have whole := NaturalRun.step t0 (run_append grid prep)
    simpa only [saved,ep,List.nil_append,List.append_nil,List.length_append,List.length_cons,
      List.length_nil,Nat.add_zero,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using whole
  · simpa only [List.append_assoc] using context
  · simpa only [List.append_assoc] using exp
  · simpa only [List.append_assoc] using input
end DirectedFlowCutGap.GridFamilyInput
