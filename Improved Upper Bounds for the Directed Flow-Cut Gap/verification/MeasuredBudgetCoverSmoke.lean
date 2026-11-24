import DirectedFlowCutGap.MeasuredBudgetCandidateLists

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (Fraction zero)
open RawNonnegativeRational (Code)

private def price (q : ℚ≥0) : Fraction := (BinaryRawRational.encode (Code.ofNNRat q)).1
private def fields {n : ℕ} (row : Vector Fraction n) : List (List Bool × List Bool) :=
  row.toList.map fun q => (q.num,q.den)
private def matrixFields {n : ℕ} (row : RationalEdgeThresholds.Weights n) :
    List (List (List Bool × List Bool)) :=
  row.toList.map fields

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
  let fee := Code.div (Code.ofNat 2) (Code.ofNat 4)
  let mass := Code.ofNat 3
  let edge := MeasuredBudgetCoverCandidate.edge edgePositive edgeGraph edgePrices edgeRequests fee mass
  let plainEdge := ConcurrentEdgeMassBudget.solve edgePositive edgeGraph edgePrices edgeRequests fee.value mass.value
  unless matrixFields edge.1 == matrixFields plainEdge &&
      0 < edge.2 && edge.2 ≤ MeasuredBudgetCoverCandidate.edgeWork 2 1 3 2 2 do
    throw (IO.userError "measured edge budget changed an emitted field or exceeded its proved charge")
  IO.println s!"PASS a raw 2/4 edge budget preserved every canonical length field and charged {edge.2}"
  let vertex := MeasuredBudgetCoverCandidate.vertex vertexPositive vertexGraph vertexPrices vertexRequests fee mass
  let plainVertex := ConcurrentVertexBudget.candidate vertexPositive vertexGraph vertexPrices vertexRequests fee.value mass.value
  unless fields vertex.1 == fields plainVertex &&
      0 < vertex.2 && vertex.2 ≤ MeasuredBudgetCoverCandidate.vertexWork 3 2 4 2 2 do
    throw (IO.userError "measured vertex budget changed an emitted field or exceeded its proved charge")
  IO.println s!"PASS the corresponding vertex budget preserved every canonical length field and charged {vertex.2}"
  let all := MeasuredBudgetCandidateLists.edge edgePositive edgeGraph edgePrices edgeRequests
  let plainList := ConcurrentEdgeBudgetGrid.candidates edgePositive edgeGraph edgePrices edgeRequests
  unless all.1.map matrixFields == plainList.map matrixFields && all.1.length == 15 && edge.2 < all.2 do
    throw (IO.userError "measuring the entire edge candidate list changed the order, output or charge")
  IO.println s!"PASS all {all.1.length} edge candidates retained their order and canonical fields with total measured charge {all.2}"
