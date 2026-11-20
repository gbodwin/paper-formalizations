import DirectedFlowCutGap.PaidDirectEdgeWire
import DirectedFlowCutGap.PaidFramedVertexWire
open DirectedFlowCutGap BinaryArithmetic

private def takeBit : Bits → PhysicalCoverAccess.Read ((Bool × ℕ) × Bits)
  | [] => (none,7)
  | b::tail => (some ((b,13),tail),13)

private def checkSamples : IO Unit := do
  let partialTape := PaidVertexAmplification.samples takeBit 3 [true,false]
  unless partialTape.1.isNone && partialTape.2 == 45 do
    throw (IO.userError "repeated sampling lost the work of earlier samples")
  let completeTape := PaidVertexAmplification.samples takeBit 2 [false,true,true]
  let some (samples,rest) := completeTape.1 | throw (IO.userError "two samples exhausted a three-bit tape")
  unless (List.ofFn fun i => (samples i).1) == [false,true] && rest == [true] && completeTape.2 == 35 do
    throw (IO.userError "repeated sampling lost its order, suffix, or recorded work")
  IO.println s!"PASS repeated sampling preserved paid late exhaustion {partialTape.2} and successful charge {completeTape.2} with suffix {rest}"

private def checkVertex : IO Unit := do
  let d : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
  let source := SourcePacking.encode d.costs d.adjacency d.demands
  let tape : Bits := [true,false]
  let r := PaidFramedVertexWire.vertexWithCost 0 .mass source tape
  let some ⟨n,output⟩ := r.1 | throw (IO.userError "the empty original vertex input failed")
  let .cut mask := output.output | throw (IO.userError "the empty vertex input did not return a cut")
  unless n == 0 && mask.toList.isEmpty && output.suffix == tape &&
      0 < output.dispatch && 0 < output.readback && 0 < output.roundingAndSelection &&
      output.dispatch+output.readback+output.roundingAndSelection < r.2 do
    throw (IO.userError "the empty vertex input lost a phase, source charge or unread tape")
  IO.println s!"PASS paid original vertex wire with empty cut, suffix {output.suffix}, all-phase charge {r.2}"

private def checkEdge : IO Unit := do
  let d : EncodedEdgeInput.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],
      #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode d
  let tape : Bits := [true,false,true]
  let r := PaidDirectEdgeWire.edgeWithCost 0 .size source tape
  let some ⟨n,output⟩ := r.1 | throw (IO.userError "the paid original edge input failed")
  let .cut mask := output.output | throw (IO.userError "the original edge input did not return a cut")
  unless n == 2 && source.length == 44 && mask.toList.map Vector.toList == [[false,true],[false,false]] &&
      output.suffix == tape && output.dispatch == 1728762983 && output.readback == 22941270 &&
      output.roundingAndSelection == 31975505 && output.dispatch+output.readback+output.roundingAndSelection < r.2 do
    throw (IO.userError "the paid edge entry changed a result, phase charge or random suffix")
  IO.println s!"PASS paid original 44-bit edge wire, cut {mask.toList.map Vector.toList}, suffix {output.suffix}, all-phase charge {r.2}"
  let rejected := PaidDirectEdgeWire.edgeWithCost 0 .size (source++[true]) tape
  unless rejected.1.isNone && 0 < rejected.2 do
    throw (IO.userError "the trailing source bit was accepted or its charge was lost")
  IO.println s!"PASS paid original edge wire rejected trailing source with charge {rejected.2}"


def main : IO Unit := do
  checkSamples
  checkVertex
  checkEdge
