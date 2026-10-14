import DirectedFlowCutGap.FinalDispatchPrefix

namespace DirectedFlowCutGap.FinalDispatch
set_option maxRecDepth 32768
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

/-- The covers case represents exactly the ordered STATE PROJECTION of the
richer high-level Result records. It does not encode operations or other fields. -/
def Output {n : ℕ} (heap : NaturalHeap) (root : ℕ) : BinaryFractionalGuesses.Output n → Prop
  | .infeasible e => OriginalDispatch.Result heap root
      (.infeasible (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2))
  | .zero mask => OriginalDispatch.Result heap root (.zero mask.toList)
  | .covers results => ∃ tag states,heap[root]?=some (.pair tag states) ∧ heap[tag]?=some .nil ∧
      GridFamily.StateList heap states (results.map fun r => some r.state)
  | .invalid => heap[root]?=some .nil

def positiveOutput {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    BinaryFractionalGuesses.Output n :=
  match (BinaryFractionalDispatch.minimumPositive costs).1 with
  | none => .invalid
  | some j => .covers (BinaryFractionalGuesses.guesses adjacency ds costs j
      (BinaryFractionalGuesses.inputWidth costs).1).results

def inputSteps {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  RowVertices.instructionBound n+dispatchSteps adjacency costs ds+
    OriginalRowMinimum.inputSteps costs.toList+GridFamilyInput.inputSteps ds.length costs.toList+32

/-- Nonrecursive bound on original row count, demands, stored fields and matrix.
The extra original-minimum scan is intentionally and separately charged. -/
def inputBound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  RowVertices.instructionBound n+
    OriginalDispatch.inputSteps (List.ofFn (RowVertices.vertexLabel (n:=n)))
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2)) (n+1)+
    OriginalRowMinimum.inputSteps costs.toList+
    GridFamilyEnvelope.instructionBound ds.length n (LambdaRowProgram.rowBits costs.toList)+32

theorem inputSteps_bound {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    inputSteps adjacency costs ds≤inputBound adjacency costs ds := by
  have hd := OriginalDispatch.steps_bound adjacency costs RowVertices.vertexLabel RowVertices.label_numeric
    ds (n+1) (by omega) (fun i => (RowVertices.label_width i).trans (by omega))
  have hg := GridFamilyEnvelope.original_input_bound ds.length costs.toList
  simp only [Vector.length_toList] at hg
  unfold inputSteps inputBound dispatchSteps
  omega
end DirectedFlowCutGap.FinalDispatch
