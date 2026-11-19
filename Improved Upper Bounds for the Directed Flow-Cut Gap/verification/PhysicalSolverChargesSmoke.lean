import DirectedFlowCutGap.PhysicalSolverCharges

open DirectedFlowCutGap

private def vertexInput : BinaryFractionalGuesses.Input 1 :=
  ⟨#v[#v[false]], [(0, 0)], #v[BinaryRational.one]⟩

private def vertexSource : List Bool :=
  PackingSourceInput.encode (SourcePacking.capacityFields vertexInput.costs)
    (SourcePacking.matrixFields vertexInput.adjacency)
    [(List.replicate 80 false, List.replicate 91 false)]

private def edgeInput : EncodedEdgeInput.Input 1 :=
  ⟨#v[#v[false]], [(0, 0)], #v[BinaryRational.one]⟩

def main : IO Unit := do
  let tape := [true, false, true]
  match PhysicalSolverCharges.vertex 0 (fun _ => EncodedWeightedRounding.tree) vertexSource tape with
  | some ⟨n, .infeasible (s, t), (rest, used), charges⟩ =>
    unless n == 1 && s.val == 0 && t.val == 0 && rest == tape && used == 0 &&
        decide (0 < charges.dispatch ∧ 0 < charges.lookups ∧ charges.sampling = 0) do
      throw (IO.userError "the vertex result changed the obstruction, tape or charges")
  | _ => throw (IO.userError "the vertex charge pipeline lost its obstruction")
  match PhysicalSolverCharges.edge 0 EncodedEdgeSolver.sizeMode (EncodedEdgeInput.encode edgeInput) tape with
  | some ⟨n, .infeasible (some (s, t)), (rest, used), charges⟩ =>
    unless n == 1 && s.val == 0 && t.val == 0 && rest == tape && used == 0 &&
        decide (0 < charges.dispatch ∧ 0 < charges.lookups ∧ charges.sampling = 0) do
      throw (IO.userError "the edge result changed the obstruction, tape or charges")
  | _ => throw (IO.userError "the edge charge pipeline lost its original obstruction")
  IO.println "PASS source charge pipelines: actual vertex and line-graph dispatch, heap lookup and fair-bit suffix"
