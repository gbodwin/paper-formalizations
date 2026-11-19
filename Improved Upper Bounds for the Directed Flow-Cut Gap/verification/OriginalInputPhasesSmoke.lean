import DirectedFlowCutGap.PhysicalOriginalInputCompleteness
import DirectedFlowCutGap.PhysicalPreparedEdgeFamily
import DirectedFlowCutGap.ChargedEdgeDyadicLabels

open DirectedFlowCutGap BinaryRational

private def sourceParsing : IO Unit := do
  let padded : BinaryRational.Fraction := ⟨[true,false,false],[true,false,false,false],by decide⟩
  let D : BinaryFractionalGuesses.Input 1 := ⟨#v[#v[false]],[],#v[padded]⟩
  let graph := PhysicalSourceDispatch.input D
  let tape := [false,true,true]
  let parsed := ChargedSourceAssembly.vertex graph
  match parsed.1 with
  | some ⟨n,decoded⟩ =>
    let fields := decoded.costs.toList.map (fun q => (q.num,q.den))
    unless n == 1 && fields == [(padded.num,padded.den)] && decoded.demands.isEmpty &&
        0 < parsed.2 && parsed.2 ≤ ChargedSourceAssembly.parseBudget graph.length do
      throw (IO.userError "charged vertex parser changed supplied fields or exceeded its bound")
  | none => throw (IO.userError "charged vertex parser rejected the original encoding")
  let extra := ChargedSourceAssembly.vertex (graph ++ [true])
  let cut := PhysicalOriginalInputSolvers.vertexWithCost 0 .mass graph tape
  unless extra.1.isNone && cut.1.isSome && cut.2 == parsed.2 do
    throw (IO.userError "physical entry lost parser coverage or accepted trailing input")
  let truncated := ChargedSourceAssembly.edge [true]
  unless truncated.1.isNone && 0 < truncated.2 && truncated.2 ≤ ChargedSourceAssembly.parseBudget 1 do
    throw (IO.userError "truncated edge table had the wrong rejection or charge")
  IO.println "PASS charged source parsing preserves padded fractions and rejects trailing or truncated input"

private def thresholds : IO Unit := do
  let adj : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let weights : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[zero,zero]]
  let demands := ChargedEdgeThresholdDemands.demands adj weights
  unless demands.1 == [(0,1),(1,0)] && 0 < demands.2 &&
      demands.2 ≤ ChargedEdgeThresholdDemands.demandBudget 2 1 do
    throw (IO.userError "threshold equality, unreachable pair or binary price changed")
  IO.println s!"PASS binary threshold demands include equality and unreachable pairs, paid {demands.2}"

private def preparedFamily : IO Unit := do
  let input : RandomizedEdgeFamily.Input 1 := ⟨#v[#v[true]],#v[#v[one]],1,0⟩
  let tape := [true,false,true]
  let some out := PhysicalPreparedEdgeFamily.run input tape
    | throw (IO.userError "prepared family did not return")
  let some history := out.family.history | throw (IO.userError "prepared family rejected a cut")
  let pre := ChargedEdgeThresholdDemands.demands input.adjacency input.weights
  unless history.cuts.length == 5 && history.cuts.all (fun cut => decide (cut=∅)) &&
      out.family.suffix == tape && out.thresholdWork == pre.2 && 0 < out.thresholdWork && 0 < out.family.dispatch do
    throw (IO.userError "prepared family did not share its threshold list or literal tape")
  IO.println s!"PASS one measured threshold computation and five actual adaptive edge calls, threshold paid {out.thresholdWork}"

private def dyadicLabels : IO Unit := do
  let cutoff : BinaryRational.Fraction := ⟨[true],[false,false,false,false,true],by decide⟩
  let quarter : BinaryRational.Fraction := ⟨[true],[false,false,true],by decide⟩
  let threeEighths : BinaryRational.Fraction := ⟨[true,true],[false,false,false,true],by decide⟩
  let cases : List (BinaryRational.Fraction × Option ℕ) :=
    [(zero,none),(cutoff,none),(quarter,some 2),(threeEighths,some 1),(one,some 0)]
  for (weight,expected) in cases do
    let out := ChargedEdgeDyadicLabels.label 8 weight
    unless out.1.map Fin.val == expected && 0 < out.2 && out.2 ≤ ChargedEdgeDyadicLabels.labelBudget 8 5 do
      throw (IO.userError "binary dyadic label or comparison charge changed")
  IO.println "PASS binary dyadic labels cover zero, the cutoff, exact and inexact powers, and unit weight"

def main : IO Unit := do
  sourceParsing
  thresholds
  preparedFamily
  dyadicLabels
