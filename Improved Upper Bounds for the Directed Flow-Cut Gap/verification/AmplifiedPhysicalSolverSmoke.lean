import DirectedFlowCutGap.PhysicalOriginalInputSolvers
import DirectedFlowCutGap.PhysicalEdgeFamily

open DirectedFlowCutGap BinaryRational
open scoped NNRat

private def path : BinaryFractionalGuesses.Input 3 :=
  ⟨#v[#v[false,true,false],#v[false,false,true],#v[false,false,false]],[(0,2)],#v[zero,one,zero]⟩

private def integerRegimes : IO Unit := do
  let tape := [false,true,false]
  let some low := PhysicalIntegerRounding.run 2 path.adjacency 1 tape
    | throw (IO.userError "small level shortcut failed")
  let some large := PhysicalIntegerRounding.run 2 path.adjacency (2^1024) tape
    | throw (IO.userError "large level shortcut failed")
  unless low.mask == #v[true,true,true] && large.mask == #v[false,false,false] &&
      low.suffix == tape && large.suffix == tape && 0 < low.paid && 0 < large.paid do
    throw (IO.userError "incorrect easy-regime flags, tape or charge")
  IO.println "PASS deterministic cutoff branches kept the tape, including the 1,025-bit threshold"

private def vertexSource : IO Unit := do
  let input : BinaryFractionalGuesses.Input 1 := ⟨#v[#v[false]],[],#v[one]⟩
  let tape := [true,false,true]
  match PhysicalOriginalInputSolvers.vertex 1 .mass (PhysicalSourceDispatch.input input) tape with
  | some ⟨n,result⟩ =>
    match result.output with
    | .cut mask =>
      unless n == 1 && mask.toList == [false] && result.suffix == tape &&
          0 < result.dispatch && 0 < result.readback && 0 < result.roundingAndSelection do
        throw (IO.userError "original vertex source lost its cut, tape or phase charges")
    | _ => throw (IO.userError "original vertex source returned a non-cut")
  | none => throw (IO.userError "original vertex source did not run")
  IO.println "PASS original encoded vertex source, actual fractional dispatch and amplified zero-demand cut"

private def positivePlan : IO Unit := do
  let tape := [true,false,true]
  let plan : PhysicalCoverReader.Plan 3 := .covers [BinaryFractionalRows.decodeRow path.costs]
  for (name,round) in [("mass",PhysicalVertexRounding.weighted),("size",PhysicalVertexRounding.size)] do
    let some ((out,work),rest) := PhysicalVertexSampling.fromPlan path round 3 plan tape
      | throw (IO.userError s!"{name} one-row solve failed")
    match out with
    | .cut mask =>
      unless mask[1] && rest == tape && 0 < work do
        throw (IO.userError s!"{name} one-row cut or tape mismatch")
    | _ => throw (IO.userError s!"{name} one-row solver returned a non-cut")
    IO.println s!"PASS {name} positive one-row refinement cuts the internal path vertex, modeled charge {work}"

private def edgeSource : IO Unit := do
  let empty : EncodedEdgeInput.Input 0 := ⟨#v[],[],#v[]⟩
  let self : EncodedEdgeInput.Input 1 := ⟨#v[#v[false]],[(0,0)],#v[one]⟩
  let tape := [false,true]
  match PhysicalOriginalInputSolvers.edge 0 .size (EncodedEdgeInput.encode empty) tape with
  | some ⟨n,result⟩ => match result.output with
    | .cut mask =>
      unless n == 0 && mask.toList.isEmpty && result.suffix == tape && 0 < result.dispatch do
        throw (IO.userError "empty edge source did not preserve output or suffix")
    | _ => throw (IO.userError "empty edge source returned a non-cut")
  | none => throw (IO.userError "empty edge source failed")
  match PhysicalOriginalInputSolvers.edge 0 .mass (EncodedEdgeInput.encode self) tape with
  | some ⟨n,result⟩ => match result.output with
    | .infeasible (some (s,t)) =>
      unless n == 1 && s.val == 0 && t.val == 0 && result.suffix == tape && 0 < result.dispatch do
        throw (IO.userError "self-demand edge source lost its original witness")
    | _ => throw (IO.userError "self-demand edge source returned an incorrect tag")
  | none => throw (IO.userError "self-demand edge source failed")
  IO.println "PASS original encoded edge source, empty cut and original self-demand witness"

private def family : IO Unit := do
  let input : RandomizedEdgeFamily.Input 1 := ⟨#v[#v[false]],#v[#v[zero]],1,0,.mass⟩
  let tape := [true,false,true]
  let some out := PhysicalEdgeFamily.run input tape | throw (IO.userError "adaptive edge runner failed")
  let some history := out.history | throw (IO.userError "adaptive edge family rejected the zero-cost cuts")
  unless history.cuts.length == 3 && history.cuts.all (fun cut => decide (cut=∅)) &&
      out.suffix == tape && 0 < out.dispatch && 0 < out.readback && 0 < out.roundingAndSelection do
    throw (IO.userError "actual adaptive family lost a cut, phase charge or suffix")
  IO.println s!"PASS three actual edge solver calls produced the zero-objective family, dispatch {out.dispatch}, readback {out.readback}, rounding and selection {out.roundingAndSelection}"

private def subunitFamily : IO Unit := do
  let adj : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let half : BinaryRational.Fraction := ⟨[true],[false,true],by decide⟩
  let input := RandomizedEdgeFamily.calibratedParameters 2 1 3 adj #v[#v[zero,half],#v[zero,zero]]
  let tape := [true,false,true]
  let some out := PhysicalEdgeFamily.family input tape | throw (IO.userError "subunit-mass family failed")
  let some history := out.history | throw (IO.userError "subunit-mass family returned no history")
  unless history.cuts.length == 13 && history.cuts.all (fun cut => decide (cut=∅)) &&
      out.suffix == tape && input.confidence == 7 && out.dispatch == 0 do
    throw (IO.userError "subunit-mass family lost its horizon, confidence or suffix")
  IO.println "PASS the calibrated subunit-mass shortcut produced 13 empty cuts with the original tape"

private def positiveSource : IO Unit := do
  let tape := [true,false,true]
  let some out := PhysicalAmplifiedVertexSolver.vertex 0 .mass path tape
    | throw (IO.userError "positive original vertex source did not return")
  match out.output with
  | .cut mask =>
    unless mask[1] && out.suffix == tape && 0 < out.dispatch && 0 < out.readback &&
        0 < out.roundingAndSelection do
      throw (IO.userError "positive original source lost its internal path cut or counters")
  | _ => throw (IO.userError "positive original source returned a non-cut")
  IO.println s!"PASS positive original vertex source, dispatch {out.dispatch}, readback {out.readback}, rounding and selection {out.roundingAndSelection}"

def main (args : List String) : IO Unit := do
  integerRegimes
  vertexSource
  positivePlan
  edgeSource
  family
  subunitFamily
  if args.contains "--positive-source" then positiveSource
