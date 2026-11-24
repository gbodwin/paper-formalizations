import DirectedFlowCutGap.ConcurrentEdgeBudgetWidths
import DirectedFlowCutGap.ConcurrentEdgeOracleWork

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero)

private def price : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat (5/7))).1
private def adjacency : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def prices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,price],#v[zero,zero]]
private def requests : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]

def main : IO Unit := do
  let budgets := ConcurrentEdgeBudgetGrid.pairs adjacency prices 1
  unless budgets.length == 15 do
    throw (IO.userError "the expected rational price and mass grid did not have 15 members")
  let some plan := ConcurrentEdgeBudgetSelection.choose (by decide) adjacency prices requests |
    throw (IO.userError "the width fixture produced no actual rational plan")
  let score := plan.receipt
  let fields := plan.lengths.toList.flatMap Vector.toList
  let width := fields.foldl (fun a q => max a (max q.num.length q.den.length)) 0
  let cap := ConcurrentEdgeBudgetWidths.candidateWidth 2 1 3
  let scoreCap := ConcurrentEdgeBudgetWidths.receiptWidth 2 1 3 cap
  unless width ≤ cap && max score.num.size score.den.size ≤ scoreCap+1 &&
      score == ((5/7 : ℚ≥0)^6) do
    throw (IO.userError "the selected lengths or exact score violated their width check")
  IO.println s!"PASS 15 original-input budget pairs, maximum length-field width {width}, exact score {(score : ℚ)}"
  let initial := FractionalCover.initial (ConcurrentEdgeCover.priceRow adjacency prices)
  let searches := ConcurrentEdgeOracleWork.measuredPaths adjacency requests initial
  let searchCap := BinaryFractionalWalkBounds.shortestBound 2
    (MultiplicityCoverWidths.weightWidth 4 3 1 0+1) 2
  let some chosen := searches.1[0] | throw (IO.userError "the measured shortest call lost the original arc")
  unless chosen.edges == [(0,1)] && 0 < searches.2 && searches.2 ≤ searchCap do
    throw (IO.userError "the measured demand cell or its paid shortest-path envelope was wrong")
  IO.println s!"PASS the actual demand cell retained arc (0,1) and recorded {searches.2} shortest-path operations"
