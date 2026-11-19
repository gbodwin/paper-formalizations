import DirectedFlowCutGap

open DirectedFlowCutGap BinaryArithmetic EncodedVertexSolver

private def costs : BinaryFractionalRows.Row 3 :=
  #v[BinaryRational.one, BinaryRational.one, ⟨[true, true], [true], by decide⟩]

private def candidates : Fin 3 → Output 3 :=
  Fin.cases (.cut #v[true, false, false])
    (Fin.cases (.cut #v[false, false, true]) (fun _ => .cut #v[false, true, false]))

def main : IO Unit := do
  let result := BinaryCutPriceSelection.minimum (BinaryCutPriceSelection.cutScore costs) 2 candidates
  match result.value with
  | .cut mask =>
    unless mask[0] && !mask[1] && !mask[2] && value result.price.num == 1 &&
        value result.price.den == 1 && 0 < result.charge do
      throw (IO.userError "binary price selection changed the minimum or the tie order")
  | _ => throw (IO.userError "binary price selection lost the winning cut")
  let trace : List (EncodedArrayStorage.Instruction Bool) :=
    [.reserve 3, .load true, .reserve 2, .store false]
  let start : Bits := (9 : Nat).bits ++ [false, false]
  let out := BinaryAllocationTrace.allocate start (trace.map BinaryAllocationTrace.reservation)
  unless value out.stop == 14 && out.blocks.map (fun (p, n) => (value p, value n)) == [(9, 3), (12, 2)] &&
      0 < out.charge do
    throw (IO.userError "the binary allocator changed the block addresses or extent")
  IO.println "PASS binary deterministic steps: exact stable price selection and ordered padded-pointer allocation"
