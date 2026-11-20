import DirectedFlowCutGap.VertexSourceTerminalLayout

open DirectedFlowCutGap BinaryArithmetic
open ImmutableReferenceSimulation (Cell Heap)

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
      describe counted == expected && joined.2 == work + input.2 && readback < joined.1.2 do
    throw (IO.userError s!"the binary source changed its observation: {describe fresh} (expected {expected})")
  IO.println s!"PASS physical source {describe fresh}, {input.1.length} bits, dispatch {dispatchFee}, boundary {boundaryFee}, serialization {input.2}, cache scalar {work}, terminal readback {joined.1.2}"

private def link (first second : ℕ) : Cell Bits := .pair first.bits second.bits

private def twoRows : Heap :=
  [.nil, .flag true, .flag false, link 1 0, link 2 0, link 1 4, link 2 5, link 5 6,
   link 7 0, link 8 0, link 0 9, link 3 3, link 11 0, link 12 0, link 0 13,
   link 14 0, link 10 15, link 0 16]

private def checkArrays : IO Unit := do
  let store := twoRows.foldl CachedReferenceHeap.push CachedReferenceHeap.empty
  let root := (17 : ℕ).bits
  let result := BinaryCoverReadback.readPlanWithBitCharge 1 store root
  let some (.covers [first,second]) := result.1 |
    throw (IO.userError "the terminal parser did not return both arrays")
  let code := BinaryCoverReadback.terminalArrayCode (.covers [first,second])
  let start := 27
  let (finish,blocks) := EncodedArrayStorage.allocateTrace start code
  let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
  unless first[0].num == 1 && first[0].den == 2 && second[0].num == 1 && second[0].den == 1 &&
      code.length == 54 && finish == start + EncodedArrayStorage.fresh code &&
      value binary.stop == finish && binary.blocks.map (fun (a,b) => (value a,value b)) == blocks do
    throw (IO.userError "the terminal arrays changed their values, order or reservations")
  IO.println s!"PASS terminal arrays retained 1/2 and 1 in order, {code.length} copy instructions, {finish-start} reserved cells from address {start}"

def main : IO Unit := do
  check empty "zero mask []"
  check oneArc "obstruction (0, 1)"
  check zeroCostPath "zero mask [false, true, false]"
  checkArrays
