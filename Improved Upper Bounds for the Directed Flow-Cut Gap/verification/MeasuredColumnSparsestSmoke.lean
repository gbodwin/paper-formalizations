import DirectedFlowCutGap.MeasuredColumnSparsestRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero one)
open RawNonnegativeRational (Code)

private def edgeGraph : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def edgePrices : RationalEdgeThresholds.Weights 2 :=
  #v[#v[zero,(BinaryRawRational.encode (Code.ofNNRat (5/7))).1],#v[zero,zero]]
private theorem edgePositive : 0 < 2 := by decide

private def vertexGraph : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def vertexPrices : BinaryFractionalRows.Row 3 := #v[one,one,one]
private theorem vertexPositive : 0 < 3 := by decide

def main : IO Unit := do
  let edgeInput := (MeasuredCanonicalCover.readEdge edgeGraph edgePrices).1
  let edgeDemands : Vector (Fin 2 × Fin 2) 2 := #v[(0,1),(0,1)]
  let edgeColumn := MeasuredColumnCover.edgeOracle edgePositive edgeGraph edgeDemands edgeInput edgeInput
  let edgeOld := MeasuredCanonicalCover.edgeOracle edgePositive edgeGraph edgeDemands edgeInput edgeInput
  let arc := ConcurrentEdgeOracle.resource (0,1)
  unless edgeColumn.1.column == edgeOld.1.column &&
      MultiplicityCover.coeff edgeColumn.1.column arc == 2 && edgeOld.2 < edgeColumn.2 do
    throw (IO.userError "the measured arc scan did not count both shared path occurrences")
  IO.println s!"PASS the shared arc contributed two visits with additional column work {edgeColumn.2-edgeOld.2}"
  let vertexInput := (MeasuredCanonicalCover.readVertex vertexPrices).1
  let vertexDemands : Vector (Fin 3 × Fin 3) 3 := #v[(0,2),(0,1),(2,0)]
  let vertexColumn := MeasuredColumnCover.vertexOracle vertexPositive vertexGraph vertexDemands vertexInput vertexInput
  let vertexOld := MeasuredCanonicalCover.vertexOracle vertexPositive vertexGraph vertexDemands vertexInput vertexInput
  unless vertexColumn.1.column == #v[0,1,0] &&
      vertexColumn.1.column == vertexOld.1.column && vertexOld.2 < vertexColumn.2 do
    throw (IO.userError "the measured vertex scan counted an endpoint or a missing path")
  IO.println s!"PASS endpoint and missing-path exclusion retained column [0, 1, 0] with additional work {vertexColumn.2-vertexOld.2}"
  let tape := [true,false,true]
  let edgeRequests : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
  let edge := MeasuredColumnSparsestRound.edge edgePositive edgeGraph edgePrices edgeRequests 0 0 tape
  unless edge.1 == some (#v[#v[false,true],#v[false,false]],tape) && 1888719021 < edge.2 do
    throw (IO.userError "the column-counted edge optimizer changed the original cut or omitted its additional work")
  IO.println s!"PASS the column-counted edge solver returned the original arc and unread tape with optimizer charge {edge.2}"
  let vertexRequests : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]
  let vertex := MeasuredColumnSparsestRound.vertex vertexPositive vertexGraph vertexPrices vertexRequests 0 0 tape
  unless vertex.1 == some (#v[false,true,false],tape) && 928428018 < vertex.2 do
    throw (IO.userError "the column-counted vertex optimizer changed the original cut or omitted its additional work")
  IO.println s!"PASS the column-counted vertex solver returned the original internal cut and unread tape with optimizer charge {vertex.2}"
