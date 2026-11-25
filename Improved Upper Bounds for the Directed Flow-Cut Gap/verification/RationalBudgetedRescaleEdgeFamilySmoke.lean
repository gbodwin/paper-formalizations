import DirectedFlowCutGap.RationalBudgetedRescaleEdgeFamily

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero one)
open RationalBudgetedRescaleEdgeFamily (eligible family multiplier rescaled draw)
open RationalEdgeDecomposition (originalTotal originalWeight)

private def pack (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat q)).1

private def denseCase : IO Unit := do
  let A : BinaryFractionalWalkOracle.Adjacency 5 :=
    #v[#v[false,false,true,true,true],#v[false,false,true,true,true],
       #v[false,false,false,true,false],#v[false,false,false,false,true],#v[false,false,false,false,false]]
  let w : RationalEdgeThresholds.Weights 5 :=
    #v[#v[zero,zero,one,one,one],#v[zero,zero,one,one,one],
       #v[zero,zero,zero,pack (1/10),zero],#v[zero,zero,zero,zero,pack (9/10)],
       #v[zero,zero,zero,zero,zero]]
  let q := rescaled A w
  let pruned := RationalPrunedEdgeFamily.pruned A w
  unless !RationalTrimmedEdgeFamily.keepsDemands A w &&
      RationalPositiveArcEdgeFamily.count A pruned == 8 && eligible A w &&
      originalTotal A w == 7 && originalTotal A q == 7 && multiplier A w == 10/9 &&
      originalWeight A q (0,2) == 1 && originalWeight A q (2,3) == 0 && originalWeight A q (3,4) == 1 do
    throw (IO.userError "the budgeted guard failed to recover the dense tight demand")
  IO.println "PASS eight arcs survived pruning on five vertices; rescaling restored the tight demand at the original total seven"

private def fallbackCase : IO Unit := do
  let A : BinaryFractionalWalkOracle.Adjacency 4 :=
    #v[#v[false,true,false,false],#v[false,false,true,true],#v[false,false,false,false],#v[false,false,false,false]]
  let w : RationalEdgeThresholds.Weights 4 :=
    #v[#v[zero,pack (1/8),zero,zero],#v[zero,zero,pack (7/8),pack (7/8)],
       #v[zero,zero,zero,zero],#v[zero,zero,zero,zero]]
  unless !eligible A w &&
      originalWeight A (rescaled A w) (1,2) == 15/16 &&
      originalTotal A (rescaled A w) == originalTotal A w &&
      (family A w).cuts == (RationalPrunedEdgeFamily.family A w).cuts do
    throw (IO.userError "the rejected rescaling did not use the original pruning fallback")
  IO.println "PASS a shared light arc left both rescaled legs below threshold; the sampler used the pruning fallback"

def main : IO Unit := do
  let A : BinaryFractionalWalkOracle.Adjacency 3 := #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
  let w : RationalEdgeThresholds.Weights 3 :=
    #v[#v[zero,pack (1/6),zero],#v[zero,zero,pack (5/6)],#v[zero,zero,zero]]
  unless eligible A w && multiplier A w == 6/5 && originalTotal A (rescaled A w) == 1 do
    throw (IO.userError "the single tight demand did not survive budgeted rescaling")
  let cuts := (family A w).cuts
  let width := FairBitWords.width cuts.length
  let tail := [true,false,true]
  let tape := List.replicate width false ++ tail
  let some ((some cut,_),(rest,used)) := draw A w 1 tape |
    throw (IO.userError "the rescaled family did not sample a cut")
  unless decide (cut = {(1,2)}) && rest == tail && used == width do
    throw (IO.userError "the rescaled family changed the cut or unread tape")
  IO.println s!"PASS the restored path used the original arc (1,2) and read {width} bits before the unchanged suffix"
  denseCase
  fallbackCase
  let empty : BinaryFractionalWalkOracle.Adjacency 0 := #v[]
  let emptyWeights : RationalEdgeThresholds.Weights 0 := #v[]
  unless multiplier empty emptyWeights == 1 && eligible empty emptyWeights &&
      (family empty emptyWeights).cuts == [∅] do
    throw (IO.userError "the zero budget did not retain the singleton empty cut")
  IO.println "PASS the empty graph used multiplier one and returned the singleton empty cut"
