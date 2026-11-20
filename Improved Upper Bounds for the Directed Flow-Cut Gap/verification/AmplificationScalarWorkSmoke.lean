import DirectedFlowCutGap.PaidVertexAmplification

open DirectedFlowCutGap BinaryArithmetic
open PhysicalCoverAccess (Read)

private def takeBit : Bits → Read ((Bool × ℕ) × Bits)
  | [] => (none,7)
  | b::rest => (some ((b,2),rest),if b then 65537 else 33)

def main : IO Unit := do
  let tape : Bits := [true,false,true]
  let first := PaidVertexAmplification.samplesWithCharges takeBit 2 tape
  let some (cuts,suffix) := first.1.1 | throw (IO.userError "measured successful sample walk failed")
  let late := PaidVertexAmplification.samplesWithCharges takeBit 3 [true,false]
  let early := PaidVertexAmplification.samplesWithCharges takeBit 5 []
  unless (cuts 0).1 && !(cuts 1).1 && suffix == [true] && first.1.2 == 65579 &&
      late.1.1.isNone && late.1.2 == 65589 && early.1.1.isNone && early.1.2 == 11 &&
      0 < early.2 && early.2 < late.2 do
    throw (IO.userError "measured sample sums changed an earlier observation or charged a skipped call")
  IO.println s!"PASS amplification samples kept success fee {first.1.2} and suffix {suffix}, late rejection {late.1.2}, early rejection {early.1.2}, scalar work {first.2}/{late.2}/{early.2}"
  let input : BinaryFractionalGuesses.Input 0 := ⟨#v[],[],#v[]⟩
  let round : PaidVertexSampling.Runner 0 := fun _ _ _ => (none,5)
  let previous := PaidVertexAmplification.runWithPlan input round 0 2 3 (.zero #v[]) 7 11 tape
  let measured := PaidVertexAmplification.runWithPlanScalarWork input round 0 2 3 (.zero #v[]) 7 11 tape
  let some out := measured.1.1 | throw (IO.userError "measured amplifier rejected a zero-objective input")
  let .cut mask := out.output | throw (IO.userError "measured amplifier returned a non-cut")
  unless mask.toList.isEmpty && out.suffix == tape && out.dispatch == 7 && out.readback == 11 &&
      measured.1.2 == previous.2 && 0 < measured.2 do
    throw (IO.userError "measured amplifier changed the result, paid fee or phase headers")
  IO.println s!"PASS one complete amplification with cut [], suffix {out.suffix}, retained fee {measured.1.2}, scalar work {measured.2}"
