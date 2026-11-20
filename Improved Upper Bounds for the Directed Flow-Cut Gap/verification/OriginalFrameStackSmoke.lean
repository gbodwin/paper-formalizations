import DirectedFlowCutGap.PaidFramedVertexCost
import DirectedFlowCutGap.PaidDirectEdgeWire
import DirectedFlowCutGap.FramedSolverStackLayout

open DirectedFlowCutGap BinaryArithmetic BinaryRational

private def samples : IO Unit := do
  let two : Fraction := ⟨(2 : ℕ).bits,[true],by decide⟩
  let input : BinaryFractionalGuesses.Input 3 :=
    ⟨#v[#v[false,false,false],#v[false,false,false],#v[false,false,false]],[],#v[one,two,one]⟩
  let row : FractionalCoverRawCore.RawRow 3 := #v[RawNonnegativeRational.Code.zero,
    RawNonnegativeRational.Code.zero,RawNonnegativeRational.Code.zero]
  let plan : PhysicalCoverReader.Plan 3 := .covers [row,row]
  let left : RetainedGridState.Flags 3 := #v[true,false,true]
  let right : RetainedGridState.Flags 3 := #v[false,true,false]
  let round : PaidVertexSampling.Runner 3 := fun _ _ tape => match tape with
    | [] => (none,11)
    | bit::rest => (some ⟨if bit then left else right,rest,if bit then 17 else 19⟩,23)
  let older := PaidVertexAmplification.runWithPlanRowWork input round 0 1 3 plan 7 11
  let framed := PaidVertexAmplification.runWithPlanFrameStackWork input round 0 1 3 plan 7 11
  let frames := PaidVertexAmplification.sampleFrameCode input round 0 1 3 plan
  let combined := AmplificationFrameLayout.code input round 0 1 3 plan
  let tape := [true,false,false,true,true]
  let before := older tape
  let after := framed tape
  let some actual := after.1.1 | throw (IO.userError "explicit frames failed on two complete samples")
  let some ref := before.1.1 | throw (IO.userError "reference failed on two complete samples")
  let .cut a := actual.output | throw (IO.userError "explicit frames returned a non-cut")
  let .cut b := ref.output | throw (IO.userError "reference returned a non-cut")
  unless a.toList == left.toList && a.toList == b.toList && actual.suffix == [true] && actual.suffix == ref.suffix &&
      actual.dispatch == ref.dispatch && actual.readback == ref.readback &&
      actual.roundingAndSelection == ref.roundingAndSelection && before.1.2 == after.1.2 && before.2 == after.2 &&
      (frames tape).length == 16 && EncodedArrayStorage.fresh (frames tape) == 4 &&
      (combined tape).length == 48 && EncodedArrayStorage.fresh (combined tape) == 12 do
    throw (IO.userError "resuming explicit frames changed the first tie, tape or fees")
  IO.println s!"PASS two saved sample frames preserved the first tied cut {a.toList}, suffix {actual.suffix}, fee {after.1.2} and measured work {after.2}"
  let early := framed []
  let late := framed [true,false,false]
  let oldEarly := older []
  let oldLate := older [true,false,false]
  unless early.1.1.isNone && late.1.1.isNone && oldEarly.1.1.isNone && oldLate.1.1.isNone &&
      early.1.2 == oldEarly.1.2 && early.2 == oldEarly.2 && late.1.2 == oldLate.1.2 && late.2 == oldLate.2 &&
      (frames []).isEmpty && (frames [true,false,false]).length == 8 &&
      (combined []).isEmpty && (combined [true,false,false]).length == 32 do
    throw (IO.userError "explicit frames lost work or saved a failed sample")
  IO.println s!"PASS first-row and second-sample exhaustion kept fees {early.1.2}/{late.1.2} and work {early.2}/{late.2}, saving zero/one sample frame and 0/32 modeled instructions"

private def original : IO Unit := do
  let tape : Bits := [true,false,true]
  let v : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
  let e : EncodedEdgeInput.Input 0 := ⟨#v[],[],#v[]⟩
  let vsrc := PhysicalSourceDispatch.input v
  let esrc := EncodedEdgeInput.encode e
  let va := PaidFramedVertexWire.vertexWithTerminalRowWork 0 .mass vsrc tape
  let vb := PaidFramedVertexWire.vertexWithTerminalFrameStackWork 0 .mass vsrc tape
  let ea := PaidDirectEdgeWire.edgeWithTerminalRowWork 0 .size esrc tape
  let eb := PaidDirectEdgeWire.edgeWithTerminalFrameStackWork 0 .size esrc tape
  let some ⟨_,vertex⟩ := vb.1.1 | throw (IO.userError "explicit original vertex frames failed")
  let some ⟨_,edge⟩ := eb.1.1 | throw (IO.userError "explicit original edge frames failed")
  let .cut vm := vertex.output | throw (IO.userError "original vertex result was a non-cut")
  let .cut em := edge.output | throw (IO.userError "original edge result was a non-cut")
  let vframes := FramedSolverStackLayout.vertex 0 .mass vsrc tape
  let eframes := FramedSolverStackLayout.edge 0 .size esrc tape
  unless vertex.suffix == tape && edge.suffix == tape && vm.toList.isEmpty && em.toList.isEmpty &&
      vframes.length == 8 && eframes.length == 8 &&
      va.1.2 == vb.1.2 && va.2 == vb.2 && ea.1.2 == eb.1.2 && ea.2.1.total == eb.2.1.total && ea.2.2 == eb.2.2 do
    throw (IO.userError "explicit frames changed an original solver or its accounting")
  IO.println s!"PASS explicit stacks preserved both three-bit original sources, unread tape {tape}, and recorded fees {vb.1.2}/{eb.1.2}"

def main : IO Unit := do
  samples
  original
