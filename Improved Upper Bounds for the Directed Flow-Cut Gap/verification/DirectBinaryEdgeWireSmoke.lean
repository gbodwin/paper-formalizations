import DirectedFlowCutGap.DirectBinaryEdgeWire

open DirectedFlowCutGap BinaryArithmetic

def main : IO Unit := do
  let D : EncodedEdgeInput.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],
      #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode D
  let tape : Bits := [true,false,true]
  let run := DirectBinaryEdgeWire.edgeWithCost 0 .size source tape
  let some ⟨n,r⟩ := run.1 | throw (IO.userError "the positive original edge wire exhausted its tape")
  let .cut mask := r.output | throw (IO.userError "the positive original edge wire did not return a cut")
  let malformed := DirectBinaryEdgeWire.edgeWithCost 0 .size (source++[true]) tape
  unless n == 2 && source.length == 44 &&
      mask.toList.map Vector.toList == [[false,true],[false,false]] && r.suffix == tape &&
      0 < run.2 && 0 < r.dispatch && 0 < r.readback && 0 < r.roundingAndSelection &&
      malformed.1.isNone && 0 < malformed.2 do
    throw (IO.userError "the direct binary edge wire changed its cut, tape, or phase charges")
  IO.println s!"PASS positive direct original edge wire, cut {mask.toList.map Vector.toList}, suffix {r.suffix}, parse {run.2}, binary fractional solver {r.dispatch}, readback {r.readback}, rounding and selection {r.roundingAndSelection}"
