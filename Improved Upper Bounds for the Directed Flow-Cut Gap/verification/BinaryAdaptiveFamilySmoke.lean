import DirectedFlowCutGap.BinaryEdgeFamilyCalibration

open DirectedFlowCutGap
open BinaryArithmetic BinaryRational RawNonnegativeRational
open scoped NNRat

private def normalizedFields : IO Unit := do
  let padded : Fraction := ⟨(34 : ℕ).bits ++ [false,false],(51 : ℕ).bits ++ [false],by decide⟩
  let reduced := BinaryRationalNormalize.reduce padded
  let zero := BinaryRationalNormalize.normalize ⟨0,19,by decide⟩
  unless value reduced.1.num == 2 && value reduced.1.den == 3 && 0 < reduced.2 &&
      zero.1.num == 0 && zero.1.den == 1 && 0 < zero.2 do
    throw (IO.userError "binary Euclid changed the canonical fields")
  IO.println s!"PASS binary Euclid reduced padded 34/51 to 2/3 and canonicalized a zero numerator, paid {reduced.2}"

private def loopAdj : BinaryFractionalWalkOracle.Adjacency 1 := #v[#v[true]]
private def loopWeight : RationalEdgeThresholds.Weights 1 := #v[#v[one]]

private def update : IO Unit := do
  let input : RandomizedEdgeFamily.Input 1 := ⟨loopAdj,loopWeight,1,0⟩
  let prepared := BinaryEdgeFamilyArithmetic.prepare input
  let state := BinaryEdgeFamilyState.initial 1
  let cut : RetainedGridState.PairFlags 1 := #v[#v[true]]
  let query := BinaryEdgeFamilyState.query input prepared.1 [] state
  let check := BinaryEdgeFamilyState.check query (.cut cut)
  let first := BinaryEdgeFamilyState.advance prepared.1 state cut
  let second := BinaryEdgeFamilyState.advance prepared.1 first.1 cut
  let a := first.1.prices[0]
  let b := second.1.prices[0]
  unless check.1.isSome && 0 < check.2 && a.num == 5 && a.den == 4 && b.num == 25 && b.den == 16 &&
      second.1.cuts.length == 2 && 0 < first.2 && 0 < second.2 do
    throw (IO.userError "binary checked update changed the exact retained prices")
  IO.println s!"PASS checked price update retains 5/4 then 25/16, comparison {check.2}, updates {first.2} and {second.2}"

private def actualCalls : IO Unit := do
  let tape := [true,false,true]
  let params := BinaryEdgeFamilyCalibration.calibrate 2 1 1 loopAdj loopWeight
  let some out := BinaryEdgeFamilyCalibration.run 2 1 1 loopAdj loopWeight tape
    | throw (IO.userError "calibrated adaptive entry returned no result")
  let some state := out.history | throw (IO.userError "calibrated adaptive entry rejected a cut")
  unless params.1.factor == 4 && params.1.confidence == 4 && 0 < params.2 &&
      state.cuts.length == 5 && state.cuts.all (fun X => decide (X=∅)) && out.suffix == tape &&
      0 < out.dispatch && 0 < out.readback && 0 < out.roundingAndSelection && 0 < out.arithmetic do
    throw (IO.userError "calibrated binary calls changed the horizon, history or tape")
  IO.println s!"PASS five actual calibrated binary edge calls, factor 4, confidence 4, adaptive arithmetic {out.arithmetic}"

private def subunit : IO Unit := do
  let tape := [true,false]
  let adj : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let half : Fraction := ⟨[true],[false,true],by decide⟩
  let w : RationalEdgeThresholds.Weights 2 := #v[#v[zero,half],#v[zero,zero]]
  let some out := BinaryEdgeFamilyCalibration.run 2 1 0 adj w tape
    | throw (IO.userError "binary subunit branch returned no result")
  let some state := out.history | throw (IO.userError "binary subunit branch returned no family")
  unless state.cuts.length == 13 && state.cuts.all (fun X => decide (X=∅)) &&
      out.suffix == tape && out.dispatch == 0 && 0 < out.arithmetic do
    throw (IO.userError "calibrated binary subunit family changed its exact horizon or tape")
  IO.println "PASS binary calibration returns the 13-cut subunit family without drawing"

def main : IO Unit := do
  normalizedFields
  update
  actualCalls
  subunit
