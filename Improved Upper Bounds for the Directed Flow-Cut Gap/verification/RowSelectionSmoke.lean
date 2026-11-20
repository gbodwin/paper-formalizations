import DirectedFlowCutGap.PaidVertexSampling

open DirectedFlowCutGap BinaryArithmetic BinaryRational

def main : IO Unit := do
  let two : Fraction := ⟨(2 : ℕ).bits,[true],by decide⟩
  let D : BinaryFractionalGuesses.Input 3 :=
    ⟨#v[#v[false,false,false],#v[false,false,false],#v[false,false,false]],[],#v[one,two,one]⟩
  let row : FractionalCoverRawCore.RawRow 3 := #v[RawNonnegativeRational.Code.zero,
    RawNonnegativeRational.Code.zero,RawNonnegativeRational.Code.zero]
  let plan : PhysicalCoverReader.Plan 3 := .covers [row,row]
  let left : RetainedGridState.Flags 3 := #v[true,false,true]
  let right : RetainedGridState.Flags 3 := #v[false,true,false]
  let round : PaidVertexSampling.Runner 3 := fun _ _ tape =>
    match tape with
    | [] => (none,11)
    | bit::rest => (some ⟨if bit then left else right,rest,if bit then 17 else 19⟩,23)
  let old := PaidVertexSampling.fromPlanWith D row round 3 plan
  let new := PaidVertexSampling.fromPlanWithSelectionWork D row round 3 plan
  let tape := [true,false,true]
  let some ((oldOut,oldFee),oldRest) := (old tape).1 | throw (IO.userError "earlier row walk failed")
  let some ((newOut,newFee),newRest) := (new tape).1.1 | throw (IO.userError "measured row walk failed")
  let .cut before := oldOut | throw (IO.userError "earlier row walk returned a non-cut")
  let .cut after := newOut | throw (IO.userError "measured row walk returned a non-cut")
  unless after.toList == left.toList && after.toList == before.toList && newRest == [true] &&
      newRest == oldRest && newFee == oldFee && (new tape).1.2 == (old tape).2 && (new tape).2 > 0 do
    throw (IO.userError "measured rows changed the first tied cut, tape or earlier fees")
  IO.println s!"PASS two equal-price rows kept {after.toList} and suffix {newRest}, fee {(new tape).1.2}, measured work {(new tape).2}"
  let early := new []
  let late := new [true]
  unless early.1.1.isNone && late.1.1.isNone && early.1.2 == (old []).2 &&
      late.1.2 == (old [true]).2 && late.2 > early.2 do
    throw (IO.userError "measured row walk lost already incurred work on tape exhaustion")
  IO.println s!"PASS early and second-row exhaustion kept earlier fees {early.1.2}/{late.1.2} and measured work {early.2}/{late.2}"
