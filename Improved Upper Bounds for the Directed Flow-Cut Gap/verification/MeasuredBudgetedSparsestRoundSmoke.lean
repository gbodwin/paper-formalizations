import DirectedFlowCutGap.MeasuredBudgetedSparsestRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero one)
open RawNonnegativeRational (Code)

private def edgeGraph : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def edgePrices : RationalEdgeThresholds.Weights 2 :=
  #v[#v[zero,(BinaryRawRational.encode (Code.ofNNRat (5/7))).1],#v[zero,zero]]
private def edgeRequests : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private theorem edgePositive : 0 < 2 := by decide

private def vertexGraph : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def vertexPrices : BinaryFractionalRows.Row 3 := #v[one,one,one]
private def vertexRequests : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]
private theorem vertexPositive : 0 < 3 := by decide

def main : IO Unit := do
  let tape := [true,false,true]
  let edge := MeasuredBudgetedSparsestRound.edge edgePositive edgeGraph edgePrices edgeRequests 0 0 tape
  let edgePlain := AmplifiedBudgetedSparsestEdge.run edgePositive edgeGraph edgePrices edgeRequests 0 0 tape
  unless edge.1 == edgePlain && edge.1 == some (#v[#v[false,true],#v[false,false]],tape) && 0 < edge.2 do
    throw (IO.userError "measuring budget construction and selection changed the original edge tape result")
  IO.println s!"PASS the original edge solver returned the same arc and unread tape with modeled optimizer charge {edge.2}"
  let vertex := MeasuredBudgetedSparsestRound.vertex vertexPositive vertexGraph vertexPrices vertexRequests 0 0 tape
  let vertexPlain := ConcurrentVertexBudgetRound.run vertexPositive vertexGraph vertexPrices vertexRequests 0 0 tape
  unless vertex.1 == vertexPlain && vertex.1 == some (#v[false,true,false],tape) && 0 < vertex.2 do
    throw (IO.userError "measuring budget construction and selection changed the original vertex tape result")
  IO.println s!"PASS the original vertex solver returned the same internal cut and unread tape with modeled optimizer charge {vertex.2}"
  let free := MeasuredBudgetedSparsestRound.vertex vertexPositive vertexGraph #v[one,zero,one] vertexRequests 0 0 tape
  unless free.1 == some (#v[false,true,false],tape) && free.2 == 0 do
    throw (IO.userError "the certified free branch charged the skipped optimizer or read the tape")
  IO.println "PASS the free vertex branch returned the original zero-price cut with zero optimizer charge and the entire tape"
