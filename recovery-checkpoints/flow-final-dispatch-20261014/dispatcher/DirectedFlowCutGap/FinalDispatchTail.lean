import DirectedFlowCutGap.FinalDispatchPositive

namespace DirectedFlowCutGap.FinalDispatch
set_option maxRecDepth 32768
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

/-- Five paid instructions preserve the returned infeasible/zero object itself.
The temporary pair saves both the original demand root and output root. -/
theorem early_return {heap : NaturalHeap} {root tag payload : ℕ} (flag : Bool)
    (look : heap[root]?=some (.pair tag payload)) (tagged : heap[tag]?=some (.flag flag))
    (next a b c : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 13320)
    (stack : List (Frame ℕ 13320)) (source : Bits) :
    NaturalRun program 5 (state heap next a b c root (⟨pc,.r3,saved⟩::stack) source 13301) []
      (state (heap++[.pair c root]) (next+1) saved.a saved.b saved.c root stack source pc) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  let ext : NaturalHeap := [.pair c root]
  have t0 : tickNatural program (state heap next a b c root frames source 13301)=
      some ⟨state (heap++ext) (next+1) a b next root frames source 13302,[],0⟩ := by rfl
  have t1 : tickNatural program (state (heap++ext) (next+1) a b next root frames source 13302)=
      some ⟨state (heap++ext) (next+1) a b next tag frames source 13303,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend look ext]
  have t2 : tickNatural program (state (heap++ext) (next+1) a b next tag frames source 13303)=
      some ⟨state (heap++ext) (next+1) a b next tag frames source 13304,[],0⟩ := by
    cases flag <;> simp [tickNatural,program,state,Registers.get,lookup_extend tagged ext,tagBranch]
  have t3 : tickNatural program (state (heap++ext) (next+1) a b next tag frames source 13304)=
      some ⟨state (heap++ext) (next+1) a b next root frames source 13305,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ext,dense]
  have t4 : tickNatural program (state (heap++ext) (next+1) a b next root frames source 13305)=
      some ⟨state (heap++ext) (next+1) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact .step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.done _)))))

theorem continue_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c root : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap c xs)
    (dispatch : OriginalDispatch.Result heap root
      (OriginalDispatch.encode RowVertices.vertexLabel (BinaryFractionalDispatch.dispatch adjacency ds costs).1))
    (next : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 13320)
    (stack : List (Frame ℕ 13320)) (source : Bits) :
    ∃ k ext out,k≤OriginalRowMinimum.inputSteps costs.toList+
        GridFamilyInput.inputSteps ds.length costs.toList+13 ∧
      NaturalRun program k (state heap next a b c root (⟨pc,.r3,saved⟩::stack) source 13301) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      Output (heap++ext) out
        (BinaryFractionalGuesses.run adjacency ds costs (BinaryFractionalGuesses.inputWidth costs).1).1 := by
  cases hd : (BinaryFractionalDispatch.dispatch adjacency ds costs).1 with
  | infeasible e =>
    simp only [hd,OriginalDispatch.encode,OriginalDispatch.Result] at dispatch
    obtain ⟨tag,payload,hp,ht,rep⟩ := dispatch
    let ext : NaturalHeap := [.pair c root]
    refine ⟨5,ext,root,by omega,?_,?_⟩
    · simpa [ext] using early_return false hp ht next a b c dense saved pc stack source
    · simp only [BinaryFractionalGuesses.run,hd,Output,OriginalDispatch.Result]
      exact ⟨tag,payload,lookup_extend hp ext,lookup_extend ht ext,EmptyDemandEdge.demand_extend rep ext⟩
  | zero mask =>
    simp only [hd,OriginalDispatch.encode,OriginalDispatch.Result] at dispatch
    obtain ⟨tag,payload,hp,ht,rep⟩ := dispatch
    let ext : NaturalHeap := [.pair c root]
    refine ⟨5,ext,root,by omega,?_,?_⟩
    · simpa [ext] using early_return true hp ht next a b c dense saved pc stack source
    · simp only [BinaryFractionalGuesses.run,hd,Output,OriginalDispatch.Result]
      exact ⟨tag,payload,lookup_extend hp ext,lookup_extend ht ext,boolList_extend rep ext⟩
  | positive witness =>
    simp only [hd,OriginalDispatch.encode,OriginalDispatch.Result] at dispatch
    obtain ⟨tag,payload,hp,ht,_witness⟩ := dispatch
    let frames := ⟨pc,.r3,saved⟩::stack
    let ep : NaturalHeap := [.pair c root]
    have t0 : tickNatural program (state heap next a b c root frames source 13301)=
        some ⟨state (heap++ep) (next+1) a b next root frames source 13302,[],0⟩ := by rfl
    have t1 : tickNatural program (state (heap++ep) (next+1) a b next root frames source 13302)=
        some ⟨state (heap++ep) (next+1) a b next tag frames source 13303,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp ep]
    have t2 : tickNatural program (state (heap++ep) (next+1) a b next tag frames source 13303)=
        some ⟨state (heap++ep) (next+1) a b next tag frames source 13306,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,lookup_extend ht ep,tagBranch]
    have t3 : tickNatural program (state (heap++ep) (next+1) a b next tag frames source 13306)=
        some ⟨state (heap++ep) (next+1) a b c tag frames source 13307,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,ep,dense]
    obtain ⟨kp,et,out,bp,positiveRun,output⟩ := positive_return adjacency costs encoded
      (BinaryIndexedPairRead.table_extend table ep) (GraphAdjacencyProgram.matrix_extend graph ep)
      (DemandCollection.demands_extend pairs ep) (next+1) (by simp [ep,dense]) saved pc stack source
    refine ⟨kp+4,ep++et,out,by omega,?_,?_⟩
    · have whole := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 positiveRun)))
      convert whole using 1 <;> simp [state,ep,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simpa only [BinaryFractionalGuesses.run,hd,positiveOutput,List.append_assoc] using output
end DirectedFlowCutGap.FinalDispatch
