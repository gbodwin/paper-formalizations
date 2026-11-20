import DirectedFlowCutGap.PaidFramedEdgeCost
import DirectedFlowCutGap.PaidFramedVertexCost

open DirectedFlowCutGap BinaryArithmetic

private def checkVertex (tape : Bits) : IO Unit := do
  let input : BinaryFractionalGuesses.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],#v[BinaryRational.one,BinaryRational.one]⟩
  let source := PhysicalSourceDispatch.input input
  let earlier := PaidFramedVertexWire.vertexWithCost 0 .mass source tape
  let fresh := PaidFramedVertexWire.vertexWithTerminalWork 0 .mass source tape
  let some ⟨n,f⟩ := fresh.1.1 | throw (IO.userError "measured terminal vertex run failed")
  let some ⟨oldN,e⟩ := earlier.1 | throw (IO.userError "earlier vertex run failed")
  let .infeasible (s,t) := f.output | throw (IO.userError "new vertex run lost the obstruction")
  let .infeasible (a,b) := e.output | throw (IO.userError "earlier vertex run lost the obstruction")
  unless source.length == 36 && n == 2 && n == oldN && (s.val,t.val) == (0,1) &&
      (s.val,t.val) == (a.val,b.val) && f.suffix == tape && e.suffix == tape &&
      f.dispatch == e.dispatch && f.readback > e.readback &&
      f.roundingAndSelection == e.roundingAndSelection &&
      fresh.2.1 == 7668311 && fresh.2.2 == 2462 do
    throw (IO.userError "measured terminal vertex did not preserve the prior observation and reached work")
  IO.println s!"PASS 36-bit vertex obstruction ({s.val}, {t.val}), suffix {f.suffix}, dispatch {f.dispatch}, reader {e.readback} to {f.readback}, cache {fresh.2.1}, frames {fresh.2.2}"

private def checkEdge (tape : Bits) : IO Unit := do
  let input : EncodedEdgeInput.Input 0 := ⟨#v[],[],#v[]⟩
  let source := EncodedEdgeInput.encode input
  let earlier := PaidDirectEdgeWire.edgeWithJoinedWork 0 .size source tape
  let fresh := PaidDirectEdgeWire.edgeWithTerminalWork 0 .size source tape
  let some ⟨n,f⟩ := fresh.1.1 | throw (IO.userError "measured terminal edge run failed")
  let some ⟨oldN,e⟩ := earlier.1.1 | throw (IO.userError "earlier edge run failed")
  let .cut mask := f.output | throw (IO.userError "new edge run returned a non-cut")
  let .cut prior := e.output | throw (IO.userError "earlier edge run returned a non-cut")
  unless source.length == 3 && n == 0 && n == oldN &&
      mask.toList.map Vector.toList == prior.toList.map Vector.toList && f.suffix == tape && e.suffix == tape &&
      f.dispatch > e.dispatch && f.readback > e.readback && fresh.2.1.total == earlier.2.1.total &&
      fresh.2.2 == earlier.2.2 do
    throw (IO.userError "measured terminal edge did not preserve the prior observation and boundary work")
  IO.println s!"PASS 3-bit edge cut and suffix {f.suffix}, paid {earlier.1.2} to {fresh.1.2}, dispatch {f.dispatch}, reader {f.readback}, boundary {fresh.2.1.total}, frames {fresh.2.2}"
  let rejected := PaidDirectEdgeWire.edgeWithTerminalWork 0 .size (source ++ [true]) tape
  unless rejected.1.1.isNone && rejected.1.2 == 4197 && rejected.2.1.total == 0 && rejected.2.2 == fresh.2.2 do
    throw (IO.userError "trailing source visited an unreached solver phase")
  IO.println s!"PASS measured terminal edge trailing source, parser fee {rejected.1.2}, zero boundary, frames {rejected.2.2}"

def main : IO Unit := do
  let tape : Bits := [true,false,true]
  checkVertex tape
  checkEdge tape
