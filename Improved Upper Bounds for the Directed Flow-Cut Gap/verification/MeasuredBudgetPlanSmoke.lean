import DirectedFlowCutGap.MeasuredBudgetPlanSelection
import DirectedFlowCutGap.MeasuredDoublingBudgetGrid

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

private def isMass : ChargedVertexModes.Mode → Bool
  | .mass => true
  | .size => false

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
  let edge := MeasuredBudgetPlanSelection.edge edgePositive edgeGraph edgePrices edgeRequests
  let some picked := edge.1.map (MeasuredSparsityPlans.decode ConcurrentEdgeBudgetSelection.Plan.mk) |
    throw (IO.userError "the measured edge optimizer did not select a plan")
  let some plain := ConcurrentEdgeBudgetSelection.choose edgePositive edgeGraph edgePrices edgeRequests |
    throw (IO.userError "the ordinary edge optimizer did not select a plan")
  unless matrixFields picked.lengths == matrixFields plain.lengths &&
      isMass picked.mode == isMass plain.mode && picked.receipt == plain.receipt &&
      picked.receipt == ((5/7 : ℚ≥0)^6) && 0 < edge.2 do
    throw (IO.userError "the measured edge selection changed a canonical field, mode or score")
  IO.println s!"PASS the measured edge selection kept score {(picked.receipt : ℚ)} and charged {edge.2}"
  let vertex := MeasuredBudgetPlanSelection.vertex vertexPositive vertexGraph vertexPrices vertexRequests
  let some picked := vertex.1.map (MeasuredSparsityPlans.decode ConcurrentVertexBudgetSelection.Plan.mk) |
    throw (IO.userError "the measured vertex optimizer did not select a plan")
  let some plain := ConcurrentVertexBudgetSelection.choose vertexPositive vertexGraph vertexPrices vertexRequests |
    throw (IO.userError "the ordinary vertex optimizer did not select a plan")
  unless fields picked.lengths == fields plain.lengths && isMass picked.mode == isMass plain.mode &&
      picked.receipt == plain.receipt && 0 < vertex.2 do
    throw (IO.userError "the measured vertex selection changed a canonical field, mode or score")
  IO.println s!"PASS the measured vertex selection kept score {(picked.receipt : ℚ)} and charged {vertex.2}"
  let lo := Code.div (Code.ofNat 2) (Code.ofNat 4)
  let hi := Code.ofNNRat (5/7)
  let grid := MeasuredDoublingBudgetGrid.grid lo hi
  unless grid.1.map Code.value == ConcurrentEdgeBudgetGrid.grid lo.value hi.value &&
      grid.1.length == 6 && 0 < grid.2 && grid.2 ≤ MeasuredDoublingBudgetGrid.gridWork 2 3 do
    throw (IO.userError "the measured geometric grid did not preserve the reduced rational boundary")
  IO.println s!"PASS the raw 2/4 to 5/7 grid retained all {grid.1.length} original entries with charge {grid.2}"
