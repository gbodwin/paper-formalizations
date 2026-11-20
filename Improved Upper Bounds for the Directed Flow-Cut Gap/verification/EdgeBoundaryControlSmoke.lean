import DirectedFlowCutGap.PaidFramedEdgeCost

open DirectedFlowCutGap BinaryArithmetic
open RawNonnegativeRational (Code)

def main : IO Unit := do
  let input : EncodedEdgeInput.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],
      #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode input
  let tape : Bits := [true,false,true]
  let measured := PaidDirectEdgeWire.edgeWithBoundaryControl 0 .size source tape
  let some ⟨n,out⟩ := measured.1.1 | throw (IO.userError "the measured edge source failed")
  let .cut cut := out.output | throw (IO.userError "the measured edge source returned a non-cut")
  let work := measured.2
  unless source.length == 44 && n == 2 && cut.toList.map Vector.toList == [[false,true],[false,false]] &&
      out.suffix == tape && measured.1.2 == 1784110573 && work.line == 168857 &&
      0 < work.prices && 0 < work.output do
    throw (IO.userError "edge boundary measurement changed the original result, tape or fee")
  IO.println s!"PASS original 44-bit edge cut and suffix {out.suffix}, legacy fee {measured.1.2}, prices {work.prices}, line {work.line}, output {work.output}"
  let malformed := PaidDirectEdgeWire.edgeWithBoundaryControl 0 .size (source++[true]) tape
  unless malformed.1.1.isNone && malformed.1.2 == 430370 && malformed.2.total == 0 do
    throw (IO.userError "rejected source reached a boundary projection")
  IO.println s!"PASS trailing original source rejected with fee {malformed.1.2}, boundary work {malformed.2.total}"
  let raw := (PhysicalBinaryEdgeWire.decodeWithCost input).1
  let valid := BinaryEdgeProjection.outputWithControl raw (.infeasible (⟨1,by decide⟩,⟨2,by decide⟩))
  let wrong := BinaryEdgeProjection.outputWithControl raw (.infeasible (⟨5,by decide⟩,⟨2,by decide⟩))
  let .infeasible (some (u,v)) := valid.1.1 | throw (IO.userError "lost the original infeasibility witness")
  let .infeasible none := wrong.1.1 | throw (IO.userError "an arc was accepted as a witness port")
  let row : FractionalCoverRawCore.RawRow (EncodedEdgeLineInput.lineSize 2) :=
    #v[Code.ofNat 11,Code.ofNat 12,Code.ofNat 13,Code.ofNat 14,
      Code.ofNat 2,Code.ofNat 3,Code.ofNat 5,Code.ofNat 7]
  let projected := BinaryEdgeProjection.roundingInputWithControl raw row
  let lifted := BinaryEdgeProjection.toLineWithControl #v[#v[false,true],#v[false,false]]
  unless (u.val,v.val) == (0,1) && 0 < valid.2 && 0 < wrong.2 &&
      projected.1.1.weights.toList.map (fun r => r.toList.map Code.num) == [[2,3],[5,7]] &&
      0 < projected.2 && lifted.1.1.toList == [false,false,false,false,false,true,false,false] && 0 < lifted.2 do
    throw (IO.userError "measured weight, mask or witness projection changed")
  IO.println s!"PASS two witness cases {valid.2}/{wrong.2}, fractional rows {projected.2} and lifted mask {lifted.2}"
