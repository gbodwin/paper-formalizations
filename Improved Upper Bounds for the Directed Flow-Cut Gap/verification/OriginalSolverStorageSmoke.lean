import DirectedFlowCutGap.FramedChargedReservations

open DirectedFlowCutGap BinaryArithmetic EncodedArrayStorage

private def zeroVertex : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
private def zeroEdge : EncodedEdgeInput.Input 0 := ⟨#v[],[],#v[]⟩
private def selfDemand : EncodedEdgeInput.Input 1 :=
  ⟨#v[#v[false]],[(0,0)],#v[BinaryRational.one]⟩

private def checkVertex (tape : Bits) : IO Unit := do
  let source := PhysicalSourceDispatch.input zeroVertex
  let paid := PaidFramedVertexWire.vertexWithTerminalRowWork 0 .mass source tape
  let some ⟨n,answer⟩ := paid.1.1 | throw (IO.userError "the original vertex source failed")
  unless n == 0 && answer.suffix == tape && FramedVertexPackedLayout.sourceTape 0 .mass source tape == some tape do
    throw (IO.userError "the vertex schedule failed to preserve the original unread tape")
  let trailing := source ++ [true]
  unless (FramedVertexPackedLayout.sourceTape 0 .mass trailing tape).isNone &&
      (PaidFramedVertexWire.vertexWithTerminalRowWork 0 .mass trailing tape).1.1.isNone do
    throw (IO.userError "the vertex schedule accepted a source with trailing bits")
  IO.println s!"PASS original vertex schedule preserved {answer.suffix} and agreed with trailing-source rejection"

private def checkEdge (tape : Bits) : IO Unit := do
  let source := EncodedEdgeInput.encode zeroEdge
  let code := FramedEdgeTerminalArrays.wireCode 0 .size source tape
  let paid := PaidDirectEdgeWire.edgeWithTerminalRowWork 0 .size source tape
  let some ⟨n,answer⟩ := paid.1.1 | throw (IO.userError "the original empty edge source failed")
  let .cut cut := answer.output | throw (IO.userError "the original empty edge source returned a witness")
  let start : ℕ := 2^100+7
  let allocated := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
  unless n == 0 && cut.toList.isEmpty && answer.suffix == tape && code.length == 3 && fresh code == 2 &&
      value allocated.stop == start+2 && 0 < FramedChargedReservations.reservationWork start code do
    throw (IO.userError "the empty graph changed its cut, tape or terminal reservations")
  let trailing := source ++ [true]
  unless (FramedEdgeTerminalArrays.wireCode 0 .size trailing tape).isEmpty &&
      (PaidDirectEdgeWire.edgeWithTerminalRowWork 0 .size trailing tape).1.1.isNone do
    throw (IO.userError "the rejected edge source reserved terminal arrays")
  IO.println s!"PASS empty edge cut retained {answer.suffix}, reserved two terminal cells at a {start.size}-bit address and skipped them on rejection"

private def checkWitness (tape : Bits) : IO Unit := do
  let source := EncodedEdgeInput.encode selfDemand
  let paid := PaidDirectEdgeWire.edgeWithTerminalRowWork 0 .mass source tape
  let some ⟨n,answer⟩ := paid.1.1 | throw (IO.userError "the original self demand failed to return an answer")
  let .infeasible (some (s,t)) := answer.output | throw (IO.userError "the original self demand lost its witness")
  let code := FramedEdgeTerminalArrays.wireCode 0 .mass source tape
  let (last,blocks) := allocateTrace 17 code
  let binary := BinaryAllocationTrace.allocate (17 : ℕ).bits (code.map BinaryAllocationTrace.reservation)
  unless n == 1 && s.val == 0 && t.val == 0 && answer.suffix == tape && 3 < code.length &&
      value binary.stop == last && binary.blocks.map (fun (start,size) => (value start,value size)) == blocks do
    throw (IO.userError "the witness changed its endpoints, unread tape or binary terminal reservations")
  IO.println s!"PASS original self demand returned ({s.val}, {t.val}) and retained {answer.suffix}, with {code.length} terminal instructions and {fresh code} reserved cells"

def main : IO Unit := do
  let tape : Bits := [true,false,true]
  checkVertex tape
  checkEdge tape
  checkWitness tape
