import DirectedFlowCutGap.FramedDirectEdgeWire

open DirectedFlowCutGap BinaryArithmetic

def main : IO Unit := do
  let d : EncodedEdgeInput.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],
      #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode d
  let tape : Bits := [true,false,true]
  let ⟨some framed,framing⟩ := OriginalSourceFraming.readBinary (source++tape)
    | throw (IO.userError "the physical framing program rejected a complete prefix")
  unless source.length == 44 && framed.source == tape && 0 < framing do
    throw (IO.userError "framing failed to retain the unused literal bits")
  for length in List.range source.length do
    let truncated := OriginalSourceFraming.readBinary (source.take length)
    unless truncated.1.isNone && 0 < truncated.2 do
      throw (IO.userError s!"source prefix of length {length} did not produce paid rejection")
  IO.println s!"PASS physical source framing of 44-bit edge wire, all 44 proper prefixes rejected, suffix {framed.source}, {framing} bit-model operations"
  let execution := FramedDirectEdgeWire.edgeWithCost 0 .size source tape
  let some ⟨n,result⟩ := execution.1 | throw (IO.userError "the complete original edge wire failed")
  let .cut mask := result.output | throw (IO.userError "expected a cut for the feasible original edge wire")
  unless n == 2 && mask.toList.map Vector.toList == [[false,true],[false,false]] && result.suffix == tape &&
      0 < execution.2 && 0 < result.dispatch && 0 < result.readback && 0 < result.roundingAndSelection do
    throw (IO.userError "the physically framed edge call changed the solution or its recorded work")
  IO.println s!"PASS physically framed direct original edge wire, cut {mask.toList.map Vector.toList}, suffix {result.suffix}, parse {execution.2}, binary fractional solver {result.dispatch}, readback {result.readback}, rounding and selection {result.roundingAndSelection}"
  let costs := SourcePacking.capacityFields d.costs
  let matrix := SourcePacking.matrixFields d.adjacency
  let demands := SourcePacking.demandFields d.demands
  let badDenominator := ([],[false,false])::costs.drop 1
  let badMatrix := ([false,true],[false])::matrix.drop 1
  for malformed in [source++[true], PackingSourceInput.encode badDenominator matrix demands,
      PackingSourceInput.encode costs badMatrix demands] do
    let rejected := FramedDirectEdgeWire.edgeWithCost 0 .size malformed tape
    unless rejected.1.isNone && 0 < rejected.2 do
      throw (IO.userError "typed physical source validation accepted malformed data")
  IO.println "PASS physical edge input rejects trailing source, a padded zero denominator and an invalid matrix row"
