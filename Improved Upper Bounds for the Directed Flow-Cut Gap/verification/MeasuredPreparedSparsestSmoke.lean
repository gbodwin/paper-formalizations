import DirectedFlowCutGap.MeasuredPreparedSparsestRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero one)
open RawNonnegativeRational (Code)

private def edgeGraph : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def prices : RationalEdgeThresholds.Weights 2 :=
  #v[#v[zero,(BinaryRawRational.encode (Code.ofNNRat (5/7))).1],#v[zero,zero]]
private def freePrices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,zero],#v[zero,zero]]
private def edgeRequests : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private theorem edgePositive : 0 < 2 := by decide

private def vertexGraph : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def vertexPrices : BinaryFractionalRows.Row 3 := #v[one,one,one]
private def freeVertexPrices : BinaryFractionalRows.Row 3 := #v[one,zero,one]
private theorem vertexPositive : 0 < 3 := by decide

def main : IO Unit := do
  let tied := MeasuredSparsestThreshold.select #v[some Code.one,some (Code.ofNat 2)]
  match tied.1 with
  | .threshold i q =>
    unless i.val == 0 && q.value == 1 && 0 < tied.2 do
      throw (IO.userError "the measured threshold changed the old first-maximum rule")
  | _ => throw (IO.userError "the measured threshold lost the positive tie")
  let missing := MeasuredSparsestThreshold.select #v[some Code.one,none,none]
  match missing.1 with
  | .unreachable i =>
    unless i.val == 1 && missing.2 < tied.2 do
      throw (IO.userError "the measured threshold searched past the first missing demand")
  | _ => throw (IO.userError "the measured threshold treated a missing path as finite")
  IO.println s!"PASS harmonic tie kept first index at cost {tied.2}, first missing index 1 at cost {missing.2}"
  let tape := [true,false,true]
  let mask := #v[#v[false,true],#v[false,false]]
  let edge := MeasuredPreparedSparsestRound.edge edgePositive edgeGraph prices edgeRequests 0 0 tape
  unless edge.1 == some (mask,tape) && 1888856721 < edge.2 do
    throw (IO.userError "measured edge preparation changed the original cut or skipped the threshold work")
  IO.println s!"PASS the positive edge branch kept the original cut and tape at preparation charge {edge.2}"
  let freeEdge := MeasuredPreparedSparsestRound.edge edgePositive edgeGraph freePrices edgeRequests 0 0 tape
  unless freeEdge.1 == some (mask,tape) && 0 < freeEdge.2 && freeEdge.2 < edge.2 do
    throw (IO.userError "measured free edge preparation lost the cut or entered the budget optimizer")
  IO.println s!"PASS the free edge branch kept the original cut and tape at preparation charge {freeEdge.2}"
  let vertexRequests : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]
  let vertex := MeasuredPreparedSparsestRound.vertex vertexPositive vertexGraph vertexPrices vertexRequests 0 0 tape
  let vertexMask := #v[false,true,false]
  unless vertex.1 == some (vertexMask,tape) && 928560626 < vertex.2 do
    throw (IO.userError "measured vertex preparation changed the original cut or skipped the threshold work")
  IO.println s!"PASS the positive vertex branch kept the original cut and tape at preparation charge {vertex.2}"
  let mixed : Vector (Fin 3 × Fin 3) 2 := #v[(0,1),(0,2)]
  let checked := MeasuredFreeResources.vertex vertexGraph freeVertexPrices mixed
  let free := MeasuredPreparedSparsestRound.vertex vertexPositive vertexGraph freeVertexPrices mixed 0 0 tape
  unless checked.1.2.map Fin.val == some 1 &&
      free.1 == some (vertexMask,tape) && free.2 == checked.2 && 0 < free.2 do
    throw (IO.userError "the vertex free scan counted an endpoint or charged the skipped positive branch")
  IO.println s!"PASS the free vertex branch skipped the direct demand and kept the tape at charge {free.2}"
