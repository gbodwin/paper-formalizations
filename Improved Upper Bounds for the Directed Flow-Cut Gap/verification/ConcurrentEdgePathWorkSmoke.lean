import DirectedFlowCutGap.ConcurrentEdgeBudgetPathWork

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero)

private def price : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat (5/7))).1
private def adjacency : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def prices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,price],#v[zero,zero]]
private def requests : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private theorem npos : 0 < 2 := by decide

def main : IO Unit := do
  let costs := ConcurrentEdgeCover.priceRow adjacency prices
  let first := ConcurrentEdgeCoverPathWork.run npos adjacency requests costs 0
  let complete := ConcurrentEdgeCoverPathWork.run npos adjacency requests costs (FractionalCover.fuel 4)
  let after := ConcurrentEdgeCoverPathWork.advance npos adjacency requests costs complete.1
  unless 0 < first.2 && first.2 < complete.2 && after.2 == 0 && after.1.bestCost == complete.1.bestCost do
    throw (IO.userError "the paid recurrence miscounted reached searches or charged a stopped state")
  IO.println s!"PASS initial binary searches charged {first.2}, complete cover charged {complete.2}, stopped state charged zero"
  let selected := ConcurrentEdgeBudgetPathWork.choose npos adjacency prices requests
  let some selectedPlan := selected.1 | throw (IO.userError "the measured budget solver returned no plan")
  let some ordinary := ConcurrentEdgeBudgetSelection.choose npos adjacency prices requests |
    throw (IO.userError "the ordinary budget solver returned no plan")
  unless selectedPlan.receipt == ordinary.receipt &&
      selectedPlan.receipt == ((5/7 : ℚ≥0)^6) &&
      0 < selected.2 && selected.2 ≤ ConcurrentEdgeBudgetPathWork.chooseSearchBound 2 1 3 do
    throw (IO.userError "measuring the candidate searches changed the selected plan or exceeded the bound")
  IO.println s!"PASS all positive budgets retained exact score {(selectedPlan.receipt : ℚ)} and total modeled search work {selected.2}"
