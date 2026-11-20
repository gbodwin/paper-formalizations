import DirectedFlowCutGap.PaidFramedEdgeCost
import DirectedFlowCutGap.PaidFramedVertexCost

open DirectedFlowCutGap BinaryArithmetic

private def vertex (tape : Bits) : IO Unit := do
  let graph : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
  let source := PhysicalSourceDispatch.input graph
  let old := PaidFramedVertexWire.vertexWithTerminalScalarWork 0 .mass source tape
  let new := PaidFramedVertexWire.vertexWithTerminalSelectionWork 0 .mass source tape
  let some ⟨n,out⟩ := new.1.1 | throw (IO.userError "measured vertex selection failed")
  let some ⟨oldN,prior⟩ := old.1.1 | throw (IO.userError "earlier vertex selection failed")
  let .cut mask := out.output | throw (IO.userError "measured vertex selection returned a non-cut")
  let .cut before := prior.output | throw (IO.userError "earlier vertex selection returned a non-cut")
  unless n == 0 && n == oldN && mask.toList.isEmpty && mask.toList == before.toList &&
      out.suffix == tape && prior.suffix == tape && out.dispatch == prior.dispatch &&
      out.readback == prior.readback && out.roundingAndSelection == prior.roundingAndSelection &&
      new.1.2 == old.1.2 && new.2.2 == old.2.2 && new.2.1 > old.2.1 do
    throw (IO.userError "measured vertex selection changed the original result or phase fees")
  IO.println s!"PASS original {source.length}-bit vertex kept {mask.toList} and suffix {out.suffix}, paid {new.1.2}, frames {new.2.2}, additional price work {new.2.1-old.2.1}"
  let rejected := PaidFramedVertexWire.vertexWithTerminalSelectionWork 0 .mass (source++[true]) tape
  let earlier := PaidFramedVertexWire.vertexWithTerminalScalarWork 0 .mass (source++[true]) tape
  unless rejected.1.1.isNone && rejected.1.2 == earlier.1.2 && rejected.2.1 == 0 &&
      rejected.2.2 == earlier.2.2 do
    throw (IO.userError "trailing vertex source visited price selection or lost its records")
  IO.println s!"PASS trailing vertex source kept parser fee {rejected.1.2} and incurred zero selection work"

private def edge (tape : Bits) : IO Unit := do
  let graph : EncodedEdgeInput.Input 0 := ⟨#v[],[],#v[]⟩
  let source := EncodedEdgeInput.encode graph
  let old := PaidDirectEdgeWire.edgeWithTerminalScalarWork 0 .size source tape
  let new := PaidDirectEdgeWire.edgeWithTerminalSelectionWork 0 .size source tape
  let some ⟨n,out⟩ := new.1.1 | throw (IO.userError "measured edge selection failed")
  let some ⟨oldN,prior⟩ := old.1.1 | throw (IO.userError "earlier edge selection failed")
  let .cut mask := out.output | throw (IO.userError "measured edge selection returned a non-cut")
  let .cut before := prior.output | throw (IO.userError "earlier edge selection returned a non-cut")
  unless n == 0 && n == oldN && mask.toList.isEmpty &&
      mask.toList.map Vector.toList == before.toList.map Vector.toList && out.suffix == tape &&
      prior.suffix == tape && out.dispatch == prior.dispatch && out.readback == prior.readback &&
      out.roundingAndSelection == prior.roundingAndSelection && new.2.1.prices == old.2.1.prices &&
      new.2.1.line == old.2.1.line && new.2.1.output == old.2.1.output &&
      new.2.2 == old.2.2 && new.1.2 > old.1.2 do
    throw (IO.userError "measured edge selection changed the original result or boundary fields")
  IO.println s!"PASS original {source.length}-bit edge kept the cut and suffix {out.suffix}, boundaries {new.2.1.total}, frames {new.2.2}, additional price work {new.1.2-old.1.2}"

def main : IO Unit := do
  let tape : Bits := [true,false,true]
  vertex tape
  edge tape
