import DirectedFlowCutGap.PaidFramedEdgeCost
import DirectedFlowCutGap.PaidFramedVertexCost

open DirectedFlowCutGap BinaryArithmetic

private def vertex (tape : Bits) : IO Unit := do
  let input : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
  let source := PhysicalSourceDispatch.input input
  let old := PaidFramedVertexWire.vertexWithTerminalWork 0 .mass source tape
  let new := PaidFramedVertexWire.vertexWithTerminalScalarWork 0 .mass source tape
  let some ⟨n,out⟩ := new.1.1 | throw (IO.userError "measured vertex amplification failed")
  let some ⟨oldN,prior⟩ := old.1.1 | throw (IO.userError "earlier vertex runner failed")
  let .cut mask := out.output | throw (IO.userError "measured vertex amplification returned a non-cut")
  let .cut before := prior.output | throw (IO.userError "earlier vertex runner returned a non-cut")
  unless n == 0 && n == oldN && mask.toList == before.toList && out.suffix == tape && prior.suffix == tape &&
      out.dispatch == prior.dispatch && out.readback == prior.readback &&
      out.roundingAndSelection == prior.roundingAndSelection && new.1.2 == old.1.2 &&
      new.2.2 == old.2.2 && new.2.1 > old.2.1 do
    throw (IO.userError "measured vertex amplification changed the original result or phase fees")
  IO.println s!"PASS original 3-bit vertex kept cut and suffix {out.suffix}, paid {new.1.2}, frames {new.2.2}, additional scalar {new.2.1-old.2.1}"
  let rejected := PaidFramedVertexWire.vertexWithTerminalScalarWork 0 .mass (source ++ [true]) tape
  unless rejected.1.1.isNone && rejected.1.2 == 4197 && rejected.2.1 == 0 && rejected.2.2 == new.2.2 do
    throw (IO.userError "trailing vertex source visited the amplification phase")
  IO.println "PASS trailing vertex source kept parser fee 4197 and incurred zero amplification work"

private def edge (tape : Bits) : IO Unit := do
  let input : EncodedEdgeInput.Input 0 := ⟨#v[],[],#v[]⟩
  let source := EncodedEdgeInput.encode input
  let old := PaidDirectEdgeWire.edgeWithTerminalWork 0 .size source tape
  let new := PaidDirectEdgeWire.edgeWithTerminalScalarWork 0 .size source tape
  let some ⟨n,out⟩ := new.1.1 | throw (IO.userError "measured edge amplification failed")
  let some ⟨oldN,prior⟩ := old.1.1 | throw (IO.userError "earlier edge runner failed")
  let .cut mask := out.output | throw (IO.userError "measured edge amplification returned a non-cut")
  let .cut before := prior.output | throw (IO.userError "earlier edge runner returned a non-cut")
  unless n == 0 && n == oldN && mask.toList.map Vector.toList == before.toList.map Vector.toList &&
      out.suffix == tape && prior.suffix == tape && out.dispatch == prior.dispatch &&
      out.readback == prior.readback && out.roundingAndSelection == prior.roundingAndSelection &&
      new.2.1.total == old.2.1.total && new.2.2 == old.2.2 && new.1.2 > old.1.2 do
    throw (IO.userError "measured edge amplification changed the original result or boundary fields")
  IO.println s!"PASS original 3-bit edge kept cut and suffix {out.suffix}, boundaries {new.2.1.total}, frames {new.2.2}, additional scalar {new.1.2-old.1.2}"

def main : IO Unit := do
  let tape : Bits := [true,false,true]
  vertex tape
  edge tape
