import DirectedFlowCutGap.MeasuredConcurrentCover
import DirectedFlowCutGap.ConcurrentEdgeCoverPathWork

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero)
open RawNonnegativeRational (Code)

private def same {r : ℕ} (a b : MultiplicityCover.State r) : Bool :=
  a.weights == b.weights && a.best == b.best && a.bestCost == b.bestCost &&
    a.total == b.total && a.loads == b.loads

private def price (q : ℚ≥0) : BinaryRational.Fraction := (BinaryRawRational.encode (Code.ofNNRat q)).1

private def edgeGraph : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def edgePrices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,price (5/7)],#v[zero,zero]]
private def edgeRequests : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private theorem edgePositive : 0 < 2 := by decide

private def vertexGraph : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def vertexPrices : BinaryFractionalRows.Row 3 := #v[price 9,price (3/2),price 8]
private def vertexRequests : Vector (Fin 3 × Fin 3) 2 := #v[(0,2),(0,1)]
private theorem vertexPositive : 0 < 3 := by decide

def main : IO Unit := do
  let edgeFuel := FractionalCover.fuel 4
  let edge := MeasuredConcurrentCover.edgeRun edgePositive edgeGraph edgePrices edgeRequests edgeFuel
  let edgeCaps := MeasuredConcurrentCover.edgePrices edgeGraph edgePrices
  let edgeOracle := MeasuredConcurrentCover.edgeOracle edgePositive edgeGraph edgeRequests edgeCaps
  let plainEdge := ConcurrentEdgeCoverPathWork.run edgePositive edgeGraph edgeRequests
    (ConcurrentEdgeCover.priceRow edgeGraph edgePrices) edgeFuel
  let stopped := MeasuredMultiplicityCover.advance edgeCaps edgeOracle edge.stored
  unless same (MeasuredMultiplicityCover.decoded edge.stored) plainEdge.1 &&
      edge.arithmetic > 0 && edge.oracleWork > plainEdge.2 &&
      stopped.arithmetic > 0 && stopped.oracleWork == 0 &&
      same (MeasuredMultiplicityCover.decoded stopped.stored) plainEdge.1 do
    throw (IO.userError "measuring edge arithmetic changed a covering field or charged a stopped oracle call")
  IO.println s!"PASS edge cover matched all fields, arithmetic {edge.arithmetic}, path and pivot {edge.oracleWork}, stopped oracle 0"
  let vertexFuel := FractionalCover.fuel 3
  let vertex := MeasuredConcurrentCover.vertexRun vertexPositive vertexGraph vertexPrices vertexRequests vertexFuel
  let c := ConcurrentVertexCover.priceRow vertexPrices
  let plain := MultiplicityCover.run c (ConcurrentVertexOracle.oracle vertexPositive vertexGraph vertexRequests c) vertexFuel
  let actual := MeasuredMultiplicityCover.decoded vertex.stored
  unless same actual plain &&
      vertex.arithmetic > 0 && vertex.oracleWork > 0 &&
      FractionalCover.value actual.best 1 == 1 do
    throw (IO.userError "measuring vertex arithmetic changed the endpoint-excluding original cover")
  IO.println s!"PASS vertex cover matched all fields at cost {actual.bestCost}, internal length 1, arithmetic {vertex.arithmetic}, path and pivot {vertex.oracleWork}"
