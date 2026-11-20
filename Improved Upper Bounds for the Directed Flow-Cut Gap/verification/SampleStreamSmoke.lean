import DirectedFlowCutGap.PaidVertexAmplification

open DirectedFlowCutGap BinaryArithmetic

def main : IO Unit := do
  let input : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
  let plan : PhysicalCoverReader.Plan 0 := .covers [#v[]]
  let round : PaidVertexSampling.Runner 0 := fun _ _ tape =>
    match tape with
    | [] => (none,11)
    | _::rest => (some ⟨#v[],rest,17⟩,23)
  let old := PaidVertexAmplification.runWithPlanSelectionWork input round 0 2 3 plan 7 11
  let new := PaidVertexAmplification.runWithPlanStreamWork input round 0 2 3 plan 7 11
  let tape := [true,false,true,true]
  let a := old tape
  let b := new tape
  let some prior := a.1.1 | throw (IO.userError "previous amplifier failed")
  let some result := b.1.1 | throw (IO.userError "streaming amplifier failed")
  let .cut mask := result.output | throw (IO.userError "streaming amplifier returned a non-cut")
  unless mask.toList.isEmpty && result.suffix == [true] && result.suffix == prior.suffix &&
      result.dispatch == prior.dispatch && result.readback == prior.readback &&
      result.roundingAndSelection == prior.roundingAndSelection && b.1.2 == a.1.2 && b.2 > a.2 do
    throw (IO.userError "streaming changed the cut, observations or previous fees")
  IO.println s!"PASS three reached samples kept suffix {result.suffix} and fee {b.1.2}, adding {b.2-a.2} operations for fee accumulation"
  let short := [true,false]
  let c := old short
  let d := new short
  unless d.1.1.isNone && c.1.1.isNone && d.1.2 == c.1.2 && d.2 == c.2 do
    throw (IO.userError "streaming did work after the third sample failed")
  IO.println s!"PASS third-sample tape exhaustion kept incurred fee {d.1.2} and added no successful-suffix work"
