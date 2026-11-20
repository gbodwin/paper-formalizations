import DirectedFlowCutGap.PaidFramedEdgeCost

open DirectedFlowCutGap BinaryArithmetic

def main : IO Unit := do
  let graph : EncodedEdgeInput.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],
      #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode graph
  let tape : Bits := [true,false,true]
  let result := PaidDirectEdgeWire.edgeWithJoinedWork 0 .size source tape
  let some ⟨n,output⟩ := result.1.1 | throw (IO.userError "the joined original edge solver failed")
  let .cut cut := output.output | throw (IO.userError "the joined original edge solver produced a non-cut")
  let control := result.2.1
  unless source.length == 44 && n == 2 && cut.toList.map Vector.toList == [[false,true],[false,false]] &&
      output.suffix == tape && 1784834946 < result.1.2 && control.prices == 11660 && control.line == 168857 &&
      control.output == 12979 && result.2.2 == 3801 do
    throw (IO.userError "the joined edge solver changed the original observation or its boundary charges")
  IO.println s!"PASS original 44-bit joined edge preserved cut and suffix {output.suffix}, paid with gadget and projections {result.1.2}, boundaries {control.total}, frames {result.2.2}"
  let rejected := PaidDirectEdgeWire.edgeWithJoinedWork 0 .size (source++[true]) tape
  unless rejected.1.1.isNone && rejected.1.2 == 430370 && rejected.2.1.total == 0 && rejected.2.2 == 3801 do
    throw (IO.userError "trailing source charged an unvisited phase or lost its framer records")
  IO.println s!"PASS joined edge trailing rejection kept fee {rejected.1.2}, boundaries {rejected.2.1.total}, frames {rejected.2.2}"
