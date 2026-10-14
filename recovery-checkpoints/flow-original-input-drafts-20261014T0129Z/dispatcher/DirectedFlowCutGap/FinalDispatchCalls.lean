import DirectedFlowCutGap.FinalDispatchCallLift

namespace DirectedFlowCutGap.FinalDispatch
set_option maxRecDepth 32768
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
open CanonicalRationalSum GraphDiscoveryProgram

def dispatchSteps {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  OriginalDispatch.steps (List.ofFn (RowVertices.vertexLabel (n:=n)))
    (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
    (ds.map fun e => (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2))+1

theorem vertex_call {rows : List BinaryRational.Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : StoredList heap a rows) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 13320) (stack : List (Frame ℕ 13320)) (source : Bits) :
    ∃ k ext root,k ≤ RowVertices.instructionBound rows.length+1 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 12940) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Vertices (heap++ext) root (RowVertexScan.words rows.length []) := by
  obtain ⟨k,ext,scratch,root,run,rep,bound⟩ := RowVertices.enumerate input next b c d dense source
  have lift := child_return vertexLabel RowVertices.program vertex_slots run rfl rfl
    .r3 .r3 saved pc stack (by
      simp only [RowVertices.state]
      simp [program,vertexLabel,callable,RowVertices.program])
  exact ⟨k+1,ext,root,by omega,
    by simpa [RowVertices.state,vertexLabel,state,Registers.get,Registers.set] using lift,rep⟩

theorem dispatch_call {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    {heap : NaturalHeap} {a b : ℕ}
    (table : OriginalDispatch.Table heap a
      (ds.map fun e => (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2)))
    (context : OriginalDispatch.Context heap b (List.ofFn (RowVertices.vertexLabel (n:=n)))
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 13320)
    (stack : List (Frame ℕ 13320)) (source : Bits) :
    ∃ ext root,NaturalRun program (dispatchSteps adjacency costs ds+1)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 12898) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      OriginalDispatch.Result (heap++ext) root
        (OriginalDispatch.encode RowVertices.vertexLabel (BinaryFractionalDispatch.dispatch adjacency ds costs).1) := by
  obtain ⟨ext,root,_len,run,rep⟩ := OriginalDispatch.dispatch adjacency costs RowVertices.vertexLabel
    RowVertices.label_numeric ds table context next c d dense [] source
  have lift := child_return dispatchLabel OriginalDispatch.program dispatch_slots run rfl rfl
    .r3 .r3 saved pc stack (by
      simp only [OriginalDispatch.state]
      simp [program,dispatchLabel,callable,OriginalDispatch.program])
  exact ⟨ext,root,by simpa [OriginalDispatch.state,dispatchLabel,state,Registers.get,Registers.set,
    dispatchSteps,Nat.add_assoc] using lift,rep⟩

theorem minimum_call {heap : NaturalHeap} {rows : List BinaryRational.Fraction} {a : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 13320)
    (stack : List (Frame ℕ 13320)) (source : Bits) :
    ∃ k ext root,k ≤ OriginalRowMinimum.inputSteps rows+1 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 13262) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PositiveMinimum.Result (heap++ext) root (OriginalRowMinimum.result rows) := by
  obtain ⟨k,ext,root,bound,run,rep⟩ := OriginalRowMinimum.compute table next b c d dense [] source
  have lift := child_return minimumLabel OriginalRowMinimum.program minimum_slots run rfl rfl
    .r3 .r3 saved pc stack (by
      simp only [OriginalRowMinimum.state]
      simp [program,minimumLabel,callable,OriginalRowMinimum.program])
  exact ⟨k+1,ext,root,by omega,
    by simpa [OriginalRowMinimum.state,minimumLabel,state,Registers.get,Registers.set] using lift,rep⟩

theorem grid_call {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c d : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap c xs)
    (next : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 13320)
    (stack : List (Frame ℕ 13320)) (source : Bits) :
    ∃ k ext root,k ≤ GridFamilyInput.inputSteps ds.length costs.toList+1 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10758) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GridFamily.StateList (heap++ext) root
        (GridFamily.values adjacency ds costs [] (GridFamilyInput.fuel costs.toList)) := by
  obtain ⟨k,ext,root,bound,run,rep⟩ := GridFamilyInput.compute adjacency costs encoded table graph pairs
    next dense [] source
  have lift := child_return gridLabel GridFamilyInput.program grid_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨k+1,ext,root,by omega,
    by simpa [GridFamilyInput.state,gridLabel,state,Registers.get,Registers.set] using lift,rep⟩
end DirectedFlowCutGap.FinalDispatch
