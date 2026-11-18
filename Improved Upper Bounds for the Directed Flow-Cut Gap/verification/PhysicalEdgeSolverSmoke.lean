import DirectedFlowCutGap.PhysicalEdgeSolver

open DirectedFlowCutGap

private def empty : EncodedEdgeInput.Input 0 := ⟨#v[], [], #v[]⟩

private def selfDemand : EncodedEdgeInput.Input 1 :=
  ⟨#v[#v[false]], [(0, 0)], #v[BinaryRational.one]⟩

def main : IO Unit := do
  let tape := [false, true]
  match PhysicalEdgeSolver.source 0 EncodedEdgeSolver.sizeMode (EncodedEdgeInput.encode empty) tape with
  | some ⟨n, .cut mask, (rest, used), paid⟩ =>
    unless n == 0 && mask.toList.isEmpty && rest == tape && used == 0 &&
        decide (0 < paid ∧ paid ≤ PhysicalEdgeSolver.paidBound (EncodedEdgeInput.decodeInput empty)) do
      throw (IO.userError "empty edge instance changed the cut, tape, or paid charge")
  | _ => throw (IO.userError "empty edge instance did not return a cut")
  match PhysicalEdgeSolver.source 0 EncodedEdgeSolver.massMode (EncodedEdgeInput.encode selfDemand) tape with
  | some ⟨n, .infeasible (some (s, t)), (rest, used), paid⟩ =>
    unless n == 1 && s.val == 0 && t.val == 0 && rest == tape && used == 0 &&
        decide (0 < paid ∧ paid ≤ PhysicalEdgeSolver.paidBound (EncodedEdgeInput.decodeInput selfDemand)) do
      throw (IO.userError "edge self demand changed the witness, tape, or paid charge")
  | _ => throw (IO.userError "edge self demand did not return its obstruction")
  IO.println "PASS physical edge source: line-graph dispatch, paid stop, and original self-demand witness"
