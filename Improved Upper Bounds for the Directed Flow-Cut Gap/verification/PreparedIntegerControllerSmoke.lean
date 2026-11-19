import DirectedFlowCutGap.PreparedIntegerController
import DirectedFlowCutGap.EncodedSolverBits

open DirectedFlowCutGap RetainedGridState FiniteDrawTrees

private def adjacency : PairFlags 2 := #v[#v[false, true], #v[false, false]]

def main : IO Unit := do
  let tape := [true, true, false]
  let G := EncodedIntegerShortestPaths.graph adjacency
  let F := CandidateEnumeration.make 2 1
  let start := RetainedDemandMask.initial G F.base.enumeration 1 (by decide)
  let ordinary := map (fun r => (r.logged.result.cache.state.data.cut, r.operations + 5))
    (RetainedBinarySampler.run adjacency F (CandidateEnumeration.fin_vertices 2) (by decide)
      0 (IntegerEpochParameters.restart 2) (IntegerEpochParameters.fuel 2 + 1)
      (IntegerEpochParameters.fuel 2 + 1) start)
  let some (result, remaining) := EncodedSolverBits.run
      (PreparedIntegerController.preparedCore 0 adjacency 1 (by decide)) tape
    | throw (IO.userError "prepared integer core failed on a retained original demand")
  unless EncodedSolverBits.run ordinary tape == some (result, remaining) && remaining == (tape, 0) do
    throw (IO.userError "the prepared integer core changed its result, charge, or tape")
  let t := PreparedIntegerController.bitTree 2 adjacency 1 (by decide)
  let some ((out, charged), rest) := EncodedSolverBits.run t tape
    | throw (IO.userError "the prepared integer dispatcher failed")
  unless out == #v[true, true] && rest == (tape, 0) && charged ≤ PreparedIntegerController.budget 2 2 do
    throw (IO.userError "the prepared integer dispatcher changed its regime or bound")
  IO.println s!"PASS prepared integer core matched ordinary controller, word charges {result.2} and {charged}"
