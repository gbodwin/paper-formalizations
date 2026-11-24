import DirectedFlowCutGap.RationalTrimmedEdgeFamilyTape
import DirectedFlowCutGap.BinaryRawRational

open DirectedFlowCutGap
open scoped NNRat
open RawNonnegativeRational (Code)
open BinaryRational (zero)

private def pack (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (Code.ofNNRat q)).1

private def dense : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[true,true],#v[true,true]]
private def denseWeights : RationalEdgeThresholds.Weights 2 :=
  #v[#v[pack (1/8),pack 2],#v[pack (1/8),pack (1/8)]]
private def path : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def tightWeights : RationalEdgeThresholds.Weights 3 :=
  #v[#v[zero,pack (1/6),zero],#v[zero,zero,pack (5/6)],#v[zero,zero,zero]]

def main : IO Unit := do
  let cuts := (RationalTrimmedEdgeFamily.family dense denseWeights).cuts
  let wanted : Finset (Fin 2 × Fin 2) := {(0,1)}
  unless RationalTrimmedEdgeFamily.keepsDemands dense denseWeights &&
      (RationalPositiveArcEdgeFamily.positiveArcs dense denseWeights).card == 4 &&
      0 < cuts.length && cuts.all (fun cut => decide (cut = wanted)) do
    throw (IO.userError "the dense input lost its original demand, selected a light arc or used the fallback")
  let width := FairBitWords.width cuts.length
  let suffix := [true,false,true]
  let tape := List.replicate width false ++ suffix
  match RationalTrimmedEdgeFamilyTape.draw dense denseWeights 1 tape with
  | some ((some cut,_),(remaining,used)) =>
    unless decide (cut = wanted) && used == width && remaining == suffix do
      throw (IO.userError "the trimmed literal draw changed the original cut or unread tape")
  | _ => throw (IO.userError "the trimmed literal draw did not return its first cut")
  IO.println s!"PASS dense original weights retained four positive arcs, {cuts.length} uniform cuts, and used {width} literal bits"
  let originalDemand := RationalEdgeThresholds.far path tightWeights (0,2)
  let trimmedDemand := RationalEdgeThresholds.far path (RationalTrimmedEdgeFamily.trimmed path tightWeights) (0,2)
  unless originalDemand && !trimmedDemand && !RationalTrimmedEdgeFamily.keepsDemands path tightWeights do
    throw (IO.userError "the preservation test accepted a trimmed graph that loses an exact-threshold demand")
  IO.println "PASS the trimming guard rejected an input that would lose its original length-one demand"
