import DirectedFlowCutGap.MeasuredBudgetRescaleEdgeFamily

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero decode)
open MeasuredBudgetRescaleEdgeFamily (prepare prepareBudget family draw)

private def pack (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat q)).1

private def acceptedPath : IO Unit := do
  let A : BinaryFractionalWalkOracle.Adjacency 3 := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let w : RationalEdgeThresholds.Weights 3 := #v[#v[zero,pack (1/6),zero],#v[zero,zero,pack (5/6)],#v[zero,zero,zero]]
  let p := prepare A w
  let leg := decode p.proposed[1][2]
  unless p.preserves && leg.value == 1 && leg.den > 1 &&
      p.work ≤ prepareBudget 3 3 do
    throw (IO.userError "binary preparation changed the result or exceeded its bound")
  let L := (family A w).cuts
  let tail := [true,false,true]
  let tape := List.replicate (FairBitWords.width L.length) false ++ tail
  let old := RationalBudgetedRescaleEdgeFamily.draw A w 1 tape
  let result := draw A w 1 tape
  let some ((some cut,_),(rest,used)) := result |
    throw (IO.userError "the measured preparation did not produce the reference cut")
  unless decide (result = old ∧ cut = {(1,2)}) && rest == tail && used == 6 do
    throw (IO.userError "the exact draw or unread suffix changed")
  IO.println s!"PASS raw retained length {leg.num}/{leg.den} matched one; preparation charged {p.work} operations and preserved the six-bit draw"

private def rejectedFork : IO Unit := do
  let A : BinaryFractionalWalkOracle.Adjacency 4 :=
    #v[#v[false,true,false,false],#v[false,false,true,true],#v[false,false,false,false],#v[false,false,false,false]]
  let w : RationalEdgeThresholds.Weights 4 :=
    #v[#v[zero,pack (1/8),zero,zero],#v[zero,zero,pack (7/8),pack (7/8)],#v[zero,zero,zero,zero],#v[zero,zero,zero,zero]]
  let p := prepare A w
  unless !p.preserves && (decode p.proposed[1][2]).value == 15/16 &&
      p.work ≤ prepareBudget 4 4 &&
      decide ((family A w).cuts = (RationalPrunedEdgeFamily.family A w).cuts) do
    throw (IO.userError "rejected binary weights changed the pruning fallback")
  IO.println s!"PASS the shared light arc triggered the same pruning fallback after {p.work} preparation operations"

def main : IO Unit := do
  acceptedPath
  rejectedFork
  let A : BinaryFractionalWalkOracle.Adjacency 0 := #v[]
  let w : RationalEdgeThresholds.Weights 0 := #v[]
  let p := prepare A w
  unless p.preserves && p.work ≤ prepareBudget 0 0 && decide ((family A w).cuts = [∅]) do
    throw (IO.userError "the binary zero-budget case did not return the empty cut")
  IO.println s!"PASS empty preparation charged {p.work} operations and retained the singleton empty cut"
