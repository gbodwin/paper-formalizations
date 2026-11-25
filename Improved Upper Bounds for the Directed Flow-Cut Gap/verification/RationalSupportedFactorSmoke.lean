import DirectedFlowCutGap.RationalInstanceEdgeFactor
import DirectedFlowCutGap.BinaryRawRational

open DirectedFlowCutGap
open scoped NNRat
open RawNonnegativeRational (Code)
open BinaryRational (zero)

private def pack (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (Code.ofNNRat q)).1

private def bridgeGraph (bridge : Bool) : BinaryFractionalWalkOracle.Adjacency 4 :=
  #v[#v[false,true,false,false],#v[false,false,bridge,false],#v[false,false,false,true],#v[false,false,false,false]]

private def bridgeWeights : RationalEdgeThresholds.Weights 4 :=
  #v[#v[zero,pack (3/5),zero,zero],#v[zero,zero,zero,zero],#v[zero,zero,zero,pack (2/5)],#v[pack 1,zero,zero,zero]]

def main : IO Unit := do
  let A := bridgeGraph true
  let w := bridgeWeights
  let D := RationalEdgeThresholds.demands A w
  let cuts := RationalInstanceEdgeFactor.supportedMinimalCuts A w
  unless RationalEdgeThresholds.far A w (0,3) &&
      cuts.length == 2 && cuts.contains {(0,1)} && cuts.contains {(2,3)} &&
      (RationalExactEdgeOracle.candidates (bridgeGraph false) D ∅).contains ∅ &&
      RationalInstanceEdgeFactor.supportDimension A w == 2 &&
      RationalInstanceEdgeFactor.leastSupported A w == 1 do
    throw (IO.userError "the support solver lost a zero-weight bridge or used the weight of a nonedge")
  IO.println "PASS a zero-weight bridge stayed in the graph; its unit-length path required a cut and used two of sixteen price coordinates"
  let zeroWeights := (Vector.replicate 4 (Vector.replicate 4 zero) : RationalEdgeThresholds.Weights 4)
  unless RationalInstanceEdgeFactor.supportDimension A zeroWeights == 0 &&
      RationalInstanceEdgeFactor.leastSupported A zeroWeights == 0 do
    throw (IO.userError "the empty support did not return factor zero")
  IO.println "PASS empty positive support used zero price coordinates and returned factor zero"

  let triangle : BinaryFractionalWalkOracle.Adjacency 3 :=
    #v[#v[false,true,false],#v[false,false,true],#v[true,false,false]]
  let half := pack (1/2)
  let triangleWeights : RationalEdgeThresholds.Weights 3 :=
    #v[#v[zero,half,zero],#v[zero,zero,half],#v[half,zero,zero]]
  unless RationalInstanceEdgeFactor.supportDimension triangle triangleWeights == 3 &&
      RationalInstanceEdgeFactor.leastSupported triangle triangleWeights == 2 do
    throw (IO.userError "the support solver accepted a unit factor for the directed triangle")
  IO.println "PASS the directed triangle used three price coordinates and retained exact factor two"
