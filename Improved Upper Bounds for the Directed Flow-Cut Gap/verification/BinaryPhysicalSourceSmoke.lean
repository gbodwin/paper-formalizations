import DirectedFlowCutGap.PhysicalSourceReadback

open DirectedFlowCutGap BinaryArithmetic

private def empty : BinaryFractionalGuesses.Input 0 := ⟨#v[], [], #v[]⟩

private def oneArc : BinaryFractionalGuesses.Input 2 :=
  ⟨#v[#v[false, true], #v[false, false]], [(0, 1)], #v[BinaryRational.one, BinaryRational.one]⟩

private def zeroCostPath : BinaryFractionalGuesses.Input 3 :=
  ⟨#v[#v[false, true, false], #v[false, false, true], #v[false, false, false]],
    [(0, 2)], #v[BinaryRational.one, BinaryRational.zero, BinaryRational.one]⟩

private def describe {n : ℕ} : PhysicalCoverReader.Plan n → String
  | .invalid => "invalid"
  | .zero mask => s!"zero mask {mask.toList}"
  | .infeasible (s,t) => s!"obstruction ({s.val}, {t.val})"
  | .covers rows => s!"covers for {rows.length} prices"

private def check {n : ℕ} (D : BinaryFractionalGuesses.Input n) (expected : String) : IO Unit := do
  let input := BinarySourceSerialization.run D
  let fuel := BinarySourceFuel.compute input.1.length
  let some (previous, charged) := PhysicalSourceBinaryCache.reference input.1 |
    throw (IO.userError "the original fractional dispatcher did not stop")
  let (plan, readback) := BinaryCoverReadback.readPlanCached n previous.store previous.registers.d
  let some old := plan | throw (IO.userError "the original returned store did not contain a plan")
  let (measured, work) := PhysicalSourceReadback.runWithCacheCharge D
  let some (fresh, dispatchFee, boundaryFee) := measured |
    throw (IO.userError "the binary fractional dispatcher did not return a plan")
  let joined := PhysicalSourceReadback.runWithBitCharges D
  let some counted := joined.1.1 | throw (IO.userError "the counted terminal readback did not return a plan")
  unless describe fresh == expected && describe fresh == describe old && dispatchFee == charged &&
      boundaryFee == readback + input.2 + fuel.2 && 0 < work &&
      describe counted == expected && joined.2 == work && readback < joined.1.2 do
    throw (IO.userError s!"the binary source changed its observation: {describe fresh} (expected {expected})")
  IO.println s!"PASS physical source {describe fresh}, {input.1.length} bits, dispatch {dispatchFee}, boundary {boundaryFee}, cache scalar {work}, terminal readback {joined.1.2}"

def main : IO Unit := do
  check empty "zero mask []"
  check oneArc "obstruction (0, 1)"
  check zeroCostPath "zero mask [false, true, false]"
