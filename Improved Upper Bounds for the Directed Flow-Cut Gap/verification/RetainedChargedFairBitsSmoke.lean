import DirectedFlowCutGap.RetainedChargedFairBits
import DirectedFlowCutGap.EncodedSolverBits

open DirectedFlowCutGap RetainedGridState

private def active : PairFlags 2 := #v[#v[false, true], #v[false, false]]

def main : IO Unit := do
  let bits := List.replicate 6 true ++ [false, true]
  let sample := RetainedChargedFairBits.sample 2 (by decide : 0 < 3) active
  match EncodedSolverBits.run sample bits with
  | some ((tape, charged), suffix, used) =>
    let actual := RetainedTapeInput.materialize (by decide : 0 < 3) active tape
    unless charged == 6 && used == charged && suffix == [false, true] &&
        actual.cell (0, 1) == 0 && actual.order == [(0, 1)] do
      throw (IO.userError "the retained sampler changed its default, charge, order, or random suffix")
  | none => throw (IO.userError "the retained sampler exhausted its tape")
  IO.println "PASS retained sampler: both bounded rejections, exact charge, and retained tape suffix"
