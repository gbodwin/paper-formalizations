import DirectedFlowCutGap.PaidVertexAmplification

open DirectedFlowCutGap BinaryArithmetic BinaryRational

def main : IO Unit := do
  let two : Fraction := ⟨(2 : ℕ).bits,[true],by decide⟩
  let input : BinaryFractionalGuesses.Input 3 :=
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
  let before := PaidVertexAmplification.runWithPlanStreamWork input round 0 1 3 plan 7 11
  let after := PaidVertexAmplification.runWithPlanRowWork input round 0 1 3 plan 7 11
  let tape := [true,false,false,true,true]
  let a := before tape
  let b := after tape
  let some old := a.1.1 | throw (IO.userError "streaming amplifier failed")
  let some new := b.1.1 | throw (IO.userError "measured row amplifier failed")
  let .cut oldMask := old.output | throw (IO.userError "streaming amplifier returned a non-cut")
  let .cut newMask := new.output | throw (IO.userError "measured row amplifier returned a non-cut")
  unless newMask.toList == left.toList && newMask.toList == oldMask.toList && new.suffix == [true] &&
      new.suffix == old.suffix && new.dispatch == old.dispatch && new.readback == old.readback &&
      new.roundingAndSelection == old.roundingAndSelection && b.1.2 == a.1.2 && b.2 > a.2 do
    throw (IO.userError "measured rows changed the first tied cut, suffix, phase or fees")
  IO.println s!"PASS two samples with two tied rows kept {newMask.toList}, suffix {new.suffix}, fee {b.1.2}, extra work {b.2-a.2}"
  let early := after []
  let late := after [true,false,false]
  let earlyPrior := before []
  let latePrior := before [true,false,false]
  unless early.1.1.isNone && late.1.1.isNone && earlyPrior.1.1.isNone && latePrior.1.1.isNone &&
      early.1.2 == earlyPrior.1.2 && late.1.2 == latePrior.1.2 &&
      early.2 > earlyPrior.2 && late.2-latePrior.2 > early.2-earlyPrior.2 do
    throw (IO.userError "measured rows lost work on early or second-sample exhaustion")
  IO.println s!"PASS early and second-sample exhaustion kept fees {early.1.2}/{late.1.2}, extra work {early.2-earlyPrior.2}/{late.2-latePrior.2}"
