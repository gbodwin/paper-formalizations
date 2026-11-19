import DirectedFlowCutGap.RetainedBinarySampler
import DirectedFlowCutGap.EncodedSolverBits

open DirectedFlowCutGap RetainedGridState

private def active : PairFlags 2 := #v[#v[false, true], #v[false, false]]

def main : IO Unit := do
  let bits := List.replicate 6 true ++ [false, true]
  let sample := RetainedBinarySampler.tape 2 (by decide : 0 < 3) active
  match EncodedSolverBits.run sample bits with
  | some ((tape, charged), suffix, used) =>
    let out := RetainedTapeInput.materialize (by decide : 0 < 3) active tape
    unless used == 6 && suffix == [false, true] &&
        out.cell (0, 1) == 0 && out.order == [(0, 1)] &&
        decide (used < charged ∧ charged ≤ RetainedBinarySampler.tapeBound 2 3 2) do
      throw (IO.userError "binary sampler changed its default, charge or tape")
    IO.println ("PASS binary sampler: 6 reads, retained suffix and " ++ toString charged ++ " operations")
  | none => throw (IO.userError "binary sampler exhausted its tape")
