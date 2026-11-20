import DirectedFlowCutGap.PaidFramedEdgeCost

open DirectedFlowCutGap BinaryArithmetic

def main : IO Unit := do
  let input : EncodedEdgeInput.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],
      #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode input
  let tape : Bits := [true,false,true]
  let metered := PaidDirectEdgeWire.edgeWithLineControl 0 .size source tape
  let some ⟨n,out⟩ := metered.1.1 | throw (IO.userError "the measured edge source failed")
  let .cut cut := out.output | throw (IO.userError "the measured edge source returned a non-cut")
  unless source.length == 44 && n == 2 && cut.toList.map Vector.toList == [[false,true],[false,false]] &&
      out.suffix == tape && metered.1.2 == 1784110573 && 0 < metered.2 do
    throw (IO.userError "measured line preparation changed the original edge cut, tape or legacy fee")
  IO.println s!"PASS original 44-bit edge cut {cut.toList.map Vector.toList}, suffix {out.suffix}, retained fee {metered.1.2}, line control {metered.2}"
  let rejected := PaidDirectEdgeWire.edgeWithLineControl 0 .size (source++[true]) tape
  unless rejected.1.1.isNone && rejected.1.2 == 430370 && rejected.2 == 0 do
    throw (IO.userError "the measured edge source charged line preparation after parse rejection")
  IO.println s!"PASS trailing edge source rejected with fee {rejected.1.2} and no line control charge"
