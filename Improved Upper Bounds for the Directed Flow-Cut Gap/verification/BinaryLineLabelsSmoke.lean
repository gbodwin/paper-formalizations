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
