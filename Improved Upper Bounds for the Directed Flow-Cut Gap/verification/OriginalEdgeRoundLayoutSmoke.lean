import DirectedFlowCutGap.FramedEdgeRoundLayout
import DirectedFlowCutGap.CutoffArrayStorage

open DirectedFlowCutGap BinaryArithmetic EncodedArrayStorage

private def crossedSamples : IO Unit := do
  let input : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
  let cover : PhysicalCoverReader.Plan 0 := .covers [#v[],#v[]]
  let round : PaidVertexSampling.Runner 0 := fun _ _ tape =>
    match tape with
    | [] => (none,11)
    | _::rest => (some ⟨#v[],rest,17⟩,23)
  let check := LiteralRoundSchedule.amplified input round 0 1 3 cover
  let solve := PaidVertexAmplification.runWithPlanRowWork input round 0 1 3 cover 7 11
  let short : Bits := [true,false,true]
  let trace := check short
  unless trace.1.map LiteralRoundSchedule.Visit.tape == [short,[false,true],[true],[]] &&
      trace.2.isNone && (solve short).1.1.isNone do
    throw (IO.userError "the schedule lost an attempted row or advanced beyond tape exhaustion")
  IO.println "PASS the second sample's last row was attempted at an empty tape and the literal solver failed there"
  let full : Bits := [true,false,true,false,true]
  let trace := check full
  let some out := (solve full).1.1 | throw (IO.userError "the complete literal sample sequence failed")
  unless trace.1.map LiteralRoundSchedule.Visit.tape == [full,[false,true,false,true],[true,false,true],[false,true]] &&
      trace.2 == some [true] && out.suffix == [true] do
    throw (IO.userError "the schedule changed a sample boundary or unread bit")
  IO.println "PASS two complete samples scheduled four rows and preserved the unread bit"

def main : IO Unit := do
  crossedSamples
  let edge : EncodedEdgeInput.Input 0 := ⟨#v[],[],#v[]⟩
  let source := EncodedEdgeInput.encode edge
  let tape : Bits := [true,false]
  unless (PhysicalSourceInputJoin.edge source).1.isSome &&
      (PhysicalSourceInputJoin.edge (source++[true])).1.isNone &&
      (FramedEdgeRoundLayout.sourceRounds 0 .mass source tape).isEmpty &&
      (FramedEdgeRoundLayout.sourceRounds 0 .mass (source++[true]) tape).isEmpty do
    throw (IO.userError "empty or rejected original source reached a round")
  IO.println "PASS the accepted empty edge source and trailing-source rejection both scheduled no round arrays"
  let adj : RetainedGridState.PairFlags 1 := #v[#v[false]]
  let some (within,_) := (GuardedCutoffWork.runBinary 0 adj 0 tape).1 |
    throw (IO.userError "the inside cutoff failed")
  let some (outside,_) := (GuardedCutoffWork.runBinary 0 adj 2 tape).1 |
    throw (IO.userError "the outside cutoff failed")
  let code := CutoffArrayStorage.constantMaskCode 1
  unless within.mask.toList == [true] && outside.mask.toList == [false] && within.suffix == tape &&
      outside.suffix == tape && code.length == 4 && fresh code == 3 do
    throw (IO.userError "the constant mask storage or tape changed at one of the cutoffs")
  IO.println "PASS both easy cutoffs initialized the one-bit mask, kept the tape and reserved three cells"
