import DirectedFlowCutGap.PhysicalAmplifiedBinaryEdge

open DirectedFlowCutGap
open EncodedEdgeLineInput
open RawNonnegativeRational (Code)

def main : IO Unit := do
  let zero := BinaryLineLabels.labels 0
  unless zero.1.toList.isEmpty && 0 < zero.2 do
    throw (IO.userError "zero-dimensional label preparation changed")
  IO.println s!"PASS zero-dimensional label preparation, paid {zero.2}"
  let D : Input 2 := ⟨#v[#v[false,true],#v[true,false]],[(0,1),(1,0),(0,1)],
    #v[#v[Code.zero,Code.ofNat 3],#v[Code.ofNat 5,Code.zero]]⟩
  let labels := BinaryLineLabels.labels 2
  let actual := PhysicalAmplifiedBinaryEdge.lineWithCost D
  let previous := PhysicalEdgeSolver.binaryLineInput D
  unless decide (labels.1[0] = Sum.inl (0,false)) &&
      decide (labels.1[1] = Sum.inl (0,true)) &&
      decide (labels.1[7] = Sum.inr (1,1)) &&
      decide (actual.1.adjacency = previous.adjacency) &&
      (actual.1.costs.toList.map (fun q => (q.num,q.den))) == (previous.costs.toList.map (fun q => (q.num,q.den))) &&
      (actual.1.demands.map (fun (s,t) => (s.val,t.val))) == [(1,2),(3,0),(1,2)] &&
      0 < labels.2 && labels.2 < actual.2 do
    throw (IO.userError "binary line labels changed a port, edge, price or demand")
  IO.println s!"PASS exact line ports, arcs, prices and repeated ordered demands, labels {labels.2}, line setup {actual.2}"
  let row : FractionalCoverRawCore.RawRow (lineSize 2) :=
    #v[Code.ofNat 11,Code.ofNat 12,Code.ofNat 13,Code.ofNat 14,
      Code.ofNat 2,Code.ofNat 3,Code.ofNat 5,Code.ofNat 7]
  let projected := BinaryEdgeProjection.roundingInput D row
  let mask := #v[true,true,true,true,true,true,false,true]
  let edges := BinaryEdgeProjection.toEdges D mask
  let lifted := BinaryEdgeProjection.toLine edges.1
  let good := BinaryEdgeProjection.output D (.infeasible (⟨1,by decide⟩,⟨2,by decide⟩))
  let wrong := BinaryEdgeProjection.output D (.infeasible (⟨5,by decide⟩,⟨2,by decide⟩))
  let .infeasible (some (s,t)) := good.1 | throw (IO.userError "the original witness was lost")
  let .infeasible none := wrong.1 | throw (IO.userError "an arc was accepted as a witness port")
  unless projected.1.weights.toList.map (fun r => r.toList.map Code.num) == [[2,3],[5,7]] &&
      edges.1.toList.map Vector.toList == [[false,true],[false,false]] &&
      lifted.1.toList == [false,false,false,false,false,true,false,false] &&
      s.val == 0 && t.val == 1 &&
      0 < projected.2 && projected.2 ≤ BinaryEdgeProjection.roundingBudget 2 &&
      0 < edges.2 && edges.2 ≤ BinaryEdgeProjection.readbackBudget 2 8 &&
      0 < lifted.2 && lifted.2 ≤ BinaryEdgeProjection.lineMaskBudget 2 &&
      good.2 ≤ BinaryEdgeProjection.outputBudget 2 && wrong.2 ≤ BinaryEdgeProjection.outputBudget 2 do
    throw (IO.userError "charged projection changed a row, mask, witness or bound")
  IO.println s!"PASS original rows, arc-only masks and exact witness ports, projection {projected.2}, edge copy {edges.2}, line copy {lifted.2}"
