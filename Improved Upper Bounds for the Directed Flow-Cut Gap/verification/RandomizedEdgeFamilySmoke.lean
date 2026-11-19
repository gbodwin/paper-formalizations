import DirectedFlowCutGap.RandomizedEdgeFamilyParameters

open DirectedFlowCutGap
open scoped NNRat

private def emptyGraph : RandomizedEdgeFamily.Input 1 :=
  ⟨#v[#v[false]], #v[#v[BinaryRational.zero]], 1, 0,.mass⟩

private def oneEdge : RandomizedEdgeFamily.Input 2 :=
  ⟨#v[#v[false, true], #v[false, false]],
    #v[#v[BinaryRational.zero, BinaryRational.one],
      #v[BinaryRational.zero, BinaryRational.zero]], 64, 0,.mass⟩

private def belowUnitMass : RandomizedEdgeFamily.Input 2 :=
  RandomizedEdgeFamily.calibratedParameters 2 1 3 oneEdge.adjacency
    #v[#v[BinaryRational.zero, ⟨[true], [false, true], by decide⟩],
      #v[BinaryRational.zero, BinaryRational.zero]]

def main (args : List String) : IO Unit := do
  let tape := [true, false, true] ++ List.replicate 128 false
  let some (some empty, rest, used) := EncodedSolverBits.run (RandomizedEdgeFamily.build emptyGraph) tape
    | throw (IO.userError "the checked zero-objective family failed")
  unless empty.cuts.length == 3 && empty.cuts.all (fun X => decide (X = ∅)) && rest == tape && used == 0 do
    throw (IO.userError "the zero-objective family changed its empty cuts or tape")
  IO.println "PASS actual adaptive edge oracle: complete zero-objective family of 3 cuts"
  let some (some small, rest, used) := EncodedSolverBits.run (RandomizedEdgeFamily.familyTree belowUnitMass) tape
    | throw (IO.userError "the subunit-mass family failed")
  unless small.cuts.length == 13 && small.cuts.all (fun X => decide (X = ∅)) &&
      rest == tape && used == 0 && belowUnitMass.confidence == 7 do
    throw (IO.userError "the subunit-mass family or its computed confidence changed")
  IO.println "PASS actual adaptive edge oracle: computed subunit-mass family of 13 empty cuts"
  let complete := args == ["--complete-active"]
  let rounds := if complete then RandomizedEdgeFamily.rounds oneEdge else 2
  let tree := AdaptiveOracleFailure.tree (RandomizedEdgeFamily.step oneEdge) rounds
    (some CheckedMWHistory.initial)
  let some (some active, rest, used) := EncodedSolverBits.run tree tape
    | throw (IO.userError "the encoded cut oracle did not finish its active family")
  unless active.cuts.length == (if complete then 17 else 2) &&
      active.cuts.all (fun X => decide (X = {(0, 1)})) &&
      rest == tape.drop used do
    throw (IO.userError "the active edge family changed its retained cuts or tape")
  IO.println s!"PASS actual adaptive edge oracle: {active.cuts.length} active cuts, {used} fair bits"
