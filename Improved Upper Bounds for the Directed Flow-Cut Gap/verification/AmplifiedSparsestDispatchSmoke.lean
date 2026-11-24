import DirectedFlowCutGap.AmplifiedSparsestDispatch

open DirectedFlowCutGap
open AmplifiedSparsestDispatch
open BinaryRational (zero one)

private def absent : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,false],#v[false,false]]
private def direct : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def edgePrices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[zero,zero]]
private def vertexPrices : BinaryFractionalRows.Row 2 := #v[one,one]
private def distinct : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private def self : Vector (Fin 2 × Fin 2) 1 := #v[(0,0)]
private def tape := [true,false,true]

def main : IO Unit := do
  let some (.cut edge rest) := runEdge absent edgePrices distinct 1 2 tape |
    throw (IO.userError "the disconnected edge demand did not give an empty cut")
  let some (.cut vertex tail) := runVertex absent vertexPrices distinct 1 2 tape |
    throw (IO.userError "the disconnected vertex demand did not give an empty cut")
  unless edge.toList.map Vector.toList == [[false,false],[false,false]] &&
      vertex.toList == [false,false] && rest == tape && tail == tape do
    throw (IO.userError "the disconnected branch touched the tape or selected a resource")
  IO.println "PASS disconnected demands returned both empty cuts with all bits unread"
  let some (.noSeparatingPair e) := runEdge direct edgePrices self 1 2 tape |
    throw (IO.userError "the self demand was reported separable in the edge problem")
  let some (.noSeparatingPair v) := runVertex direct vertexPrices distinct 1 2 tape |
    throw (IO.userError "the direct demand was reported separable in the vertex problem")
  let some (.noSeparatingPair noGraph) := runEdge
      (#v[] : BinaryFractionalWalkOracle.Adjacency 0) #v[] (#v[] : Vector (Fin 0 × Fin 0) 0) 1 2 tape |
    throw (IO.userError "the empty graph was reported to have a separable demand")
  unless e == tape && v == tape && noGraph == tape do
    throw (IO.userError "the no-separating-pair dispatch changed the tape")
  IO.println "PASS self, direct vertex and empty-graph inputs reported no separating pair without reading bits"
  let some (.cut original suffix) := runEdge direct edgePrices distinct 1 2 tape |
    throw (IO.userError "the direct arc did not reach the actual edge solver")
  unless original.toList.map Vector.toList == [[false,true],[false,false]] && suffix == tape do
    throw (IO.userError "the supported edge dispatch changed the original arc or remainder")
  IO.println "PASS the same direct demand reached the edge solver and cut its original arc"
