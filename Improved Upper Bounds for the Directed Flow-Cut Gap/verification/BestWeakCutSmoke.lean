import DirectedFlowCutGap.PhysicalWeakCutWire

open DirectedFlowCutGap BinaryArithmetic BinaryRational

private def checkSize : IO Unit := do
  let adj : BinaryFractionalWalkOracle.Adjacency 1 := #v[#v[true]]
  let four : Fraction := ⟨[false,false,true],[true],by decide⟩
  let w : RationalEdgeThresholds.Weights 1 := #v[#v[four]]
  let params := BinaryEdgeFamilyCalibration.calibrate 2 1 0 adj w
  unless decide (params.1.strategy = CheckedEdgeOracle.Strategy.size) &&
      params.1.factor == 4 && RandomizedEdgeFamily.rounds params.1 == 9 && 0 < params.2 do
    throw (IO.userError "calibration did not select the smaller size factor")
  let tape := [true,false,true]
  let some out := BinaryEdgeFamilyCalibration.run 2 1 0 adj w tape |
    throw (IO.userError "size-based adaptive family did not finish")
  let some history := out.history | throw (IO.userError "size-based adaptive family rejected")
  unless history.cuts.length == 9 && history.cuts.all (fun X => decide (X=∅)) &&
      out.suffix == tape && 0 < out.roundingAndSelection do
    throw (IO.userError "size-based adaptive family changed its cuts or suffix")
  IO.println s!"PASS size strategy ran all nine adaptive calls, factor 4, calibration {params.2}"

private def checkWire : IO Unit := do
  let adj : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let half : Fraction := ⟨[true,false],[false,true,false],by decide⟩
  let w : RationalEdgeThresholds.Weights 2 := #v[#v[zero,half],#v[zero,zero]]
  let params := BinaryEdgeFamilyCalibration.calibrate 2 1 0 adj w
  unless decide (params.1.strategy = CheckedEdgeOracle.Strategy.mass) do
    throw (IO.userError "tied factors did not select the mass strategy")
  let bits := PhysicalWeakCutWire.encode adj w
  let tape := [true,true,true,true,false,false,false,false,true,false]
  let decoded := PhysicalWeakCutWire.run 2 1 0 bits tape
  let some ⟨n,out⟩ := decoded.1 | throw (IO.userError "original weight wire did not finish")
  unless n == 2 && (out.cut.map Finset.card) == some 0 && out.suffix == [true,false] && 0 < decoded.2 do
    throw (IO.userError "original weight wire changed its selection or suffix")
  let trailing := PhysicalWeakCutWire.run 2 1 0 (bits++[true]) tape
  let requested : EncodedEdgeInput.Input 2 := ⟨adj,[(0,1)],#v[zero,half,zero,zero]⟩
  let manual := PhysicalWeakCutWire.run 2 1 0 (EncodedEdgeInput.encode requested) tape
  unless trailing.1.isNone && manual.1.isNone && 0 < trailing.2 && 0 < manual.2 do
    throw (IO.userError "invalid original weight wire was accepted")
  IO.println s!"PASS padded original weight wire used mass on a tie, preserved the suffix and rejected both malformed wires, setup {decoded.2}"

def main : IO Unit := do
  checkSize
  checkWire
