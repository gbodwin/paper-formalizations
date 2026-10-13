import DirectedFlowCutGap.GridFamilyInputPrefix

namespace DirectedFlowCutGap.GridFamilyInput
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
set_option maxRecDepth 32768

theorem compute {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c d : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap c xs)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 10760)) (source : Bits) :
    ∃ k ext root,k ≤ inputSteps ds.length costs.toList ∧
      NaturalRun program k (state heap next a b c d stack source 10758) []
        (state (heap++ext) (next+ext.length) a b c root stack source 10759) ∧
      GridFamily.StateList (heap++ext) root
        (GridFamily.values adjacency ds costs [] (fuel costs.toList)) := by
  let saved : Registers ℕ := ⟨a,b,c,d⟩
  let outer : Frame ℕ 10760 := ⟨10759,.r3,saved⟩
  have t0 : tickNatural program (state heap next a b c d stack source 10758)=
      some ⟨state heap next a b c d (outer::stack) source 10730,[],0⟩ := by rfl
  obtain ⟨ep,cp,xp,fp,gp,prep,context,exp,input⟩ := prepare_return adjacency costs table graph pairs
    next dense (outer::stack) source
  let localSaved : Registers ℕ := ⟨cp,xp,fp,gp⟩
  have nd : next+ep.length=(heap++ep).length := by simp [dense]
  have t1 : tickNatural program (state (heap++ep) (next+ep.length) cp xp fp gp (outer::stack) source 10735)=
      some ⟨state (heap++ep) (next+ep.length) cp xp fp gp
        (⟨10736,.r3,localSaved⟩::outer::stack) source 10178,[],0⟩ := by rfl
  obtain ⟨k,ef,root,bound,family,rep⟩ := family_call adjacency costs encoded context exp input
    (next+ep.length) gp nd localSaved 10736 (outer::stack) source
  have t2 : tickNatural program
      (state (heap++ep++ef) (next+ep.length+ef.length) cp xp fp root (outer::stack) source 10736)=
      some ⟨state (heap++ep++ef) (next+ep.length+ef.length) a b c root stack source 10759,[],0⟩ := by
    simp [tickNatural,program,state,outer,saved,Registers.get,Registers.set]
  have core := NaturalRun.step t0 (run_append prep (NaturalRun.step t1
    (run_append family (NaturalRun.step t2 (NaturalRun.done _)))))
  refine ⟨GridInputProgram.steps costs.toList+k+10,ep++ef,root,?_,?_,?_⟩
  · have h := GridInputProgram.steps_bound costs.toList
    simp only [inputSteps]
    omega
  · convert core using 1 <;>
      simp only [state,List.append_nil,List.length_append,
        List.append_assoc,Nat.add_assoc]
    all_goals omega
  · simpa only [List.append_assoc] using rep
end DirectedFlowCutGap.GridFamilyInput
