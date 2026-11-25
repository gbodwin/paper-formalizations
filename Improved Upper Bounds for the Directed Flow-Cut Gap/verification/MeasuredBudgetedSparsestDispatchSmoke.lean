import DirectedFlowCutGap.MeasuredBudgetedSparsestDispatch
open DirectedFlowCutGap
open BinaryRational (one zero)

private def tape := [true,false,true]
private def A : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def emptyGraph : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,false],#v[false,false]]
private def edgeCosts : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[zero,zero]]
private def demand : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]

def main : IO Unit := do
  let edge := MeasuredBudgetedSparsestDispatch.edge emptyGraph edgeCosts demand 2 3 tape
  let some (.cut mask rest) := edge.1 | throw (IO.userError "disconnected demand returned no cut")
  unless mask == #v[#v[false,false],#v[false,false]] && rest == tape && 0 < edge.2 do
    throw (IO.userError "disconnected demand changed the empty mask or unread tape")
  IO.println s!"PASS disconnected edge dispatch kept the empty cut and literal tape at modeled fee {edge.2}"
  let direct := MeasuredBudgetedSparsestDispatch.vertex A #v[one,one] demand 2 3 tape
  let some (.noSeparatingPair rest) := direct.1 | throw (IO.userError "a direct arc was treated as internally separable")
  unless rest == tape && 0 < direct.2 do
    throw (IO.userError "vertex dispatch charged missing work or consumed tape on a direct arc")
  IO.println s!"PASS direct vertex demand was inseparable with unread tape and modeled fee {direct.2}"
  let empty := MeasuredBudgetedSparsestDispatch.vertex #v[] #v[] #v[] 2 3 tape
  let some (.noSeparatingPair rest) := empty.1 | throw (IO.userError "empty vertex graph did not return a boundary result")
  unless rest == tape && 0 < empty.2 do
    throw (IO.userError "empty graph lost its unread bits or modeled work")
  IO.println s!"PASS empty vertex graph kept all bits with modeled fee {empty.2}"
