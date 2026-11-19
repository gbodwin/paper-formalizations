import DirectedFlowCutGap.ChargedVertexModes

open DirectedFlowCutGap BinaryRational FiniteDrawTrees
open RetainedGridState (Flags)

private def input : BinaryFractionalGuesses.Input 3 :=
  ⟨#v[#v[false, true, false], #v[false, false, true], #v[false, false, false]],
    [(0, 2)], #v[zero, one, zero]⟩

private def positive (mode : ChargedVertexModes.Mode) (name : String) (plan : PhysicalCoverReader.Plan 3) :
    IO Unit := do
  let tape := [true, false, true]
  let e := EncodedVertexAmplification.confidenceExponent 3 0
  let t := ChargedPhysicalVertexSolver.amplifiedFromPlan input (ChargedVertexModes.chargedRound 3 mode)
    (EncodedVertexAmplification.roundDrawBound 3) e (e + 1) plan
  let some ((out, work), rest) := EncodedSolverBits.run t tape
    | throw (IO.userError s!"{name} did not return a cut")
  match out with
  | .cut mask =>
    unless mask[1] && rest == (tape, 0) && decide (0 < work ∧ work ≤ ChargedVertexModes.budget 0 mode input) do
      throw (IO.userError s!"{name} changed its cut, tape or charge bounds")
  | _ => throw (IO.userError s!"{name} returned a non-cut result")
  IO.println s!"PASS {name} positive-cost cut, modeled rounding and selection {work}, consumed {rest.2}"

private def physical : IO Unit := do
  let some (plan, paid, lookups) := PhysicalSourceReadback.run input
    | throw (IO.userError "the positive physical source did not return its retained plan")
  match plan with
  | .covers rows =>
    unless rows.length == 9 && 0 < paid && 0 < lookups do
      throw (IO.userError "the positive physical dispatch changed the retained row count or phase charges")
  | _ => throw (IO.userError "the positive physical source did not return covers")
  positive .mass "physical mass" plan
  positive .size "physical size" plan
  IO.println s!"PASS physical prefix used nine cover rows, paid dispatch {paid}, lookups {lookups}"

private def zeroSource : IO Unit := do
  let graph : BinaryFractionalGuesses.Input 1 := ⟨#v[#v[false]], [], #v[one]⟩
  let tape := [true, false, true]
  let some r := ChargedVertexModes.run 0 .mass graph tape
    | throw (IO.userError "the zero-demand physical source did not return a result")
  match r.output with
  | .cut mask =>
    unless !mask[0] && r.tape == (tape, 0) && 0 < r.dispatch && 0 < r.lookups && 0 < r.roundingAndSelection do
      throw (IO.userError "the zero-demand physical source changed the cut, suffix or charges")
  | _ => throw (IO.userError "the zero-demand physical source lost its empty cut")
  IO.println "PASS zero-demand physical source, exact empty mask and tape"

private def tieInput : BinaryFractionalGuesses.Input 2 :=
  ⟨#v[#v[false, true], #v[false, false]], [], #v[one, one]⟩

private def tiedRound : ChargedPhysicalVertexSolver.ChargedRound 2 :=
  fun _ _ => map (fun (i : Fin 2) => (if i = 0 then #v[true, false] else #v[false, true], 17))
    (pick 2 (by decide))

private def ties : IO Unit := do
  let row := BinaryFractionalRows.decodeRow tieInput.costs
  let p : PhysicalCoverReader.Plan 2 := .covers [row, row]
  let t := ChargedPhysicalVertexSolver.amplifiedFromPlan tieInput tiedRound 1 1 3 p
  let tape := [true, false, false, true, false]
  let some ((out, paid), rest) := EncodedSolverBits.run t tape
    | throw (IO.userError "the tied physical plan did not produce an amplified result")
  match out with
  | .cut mask =>
    unless mask == #v[false, true] && rest == ([false], 4) && 68 < paid do
      throw (IO.userError "the tied selection changed draw order, winner or modeled charge")
  | _ => throw (IO.userError "the tied selection returned a non-cut result")
  unless (EncodedSolverBits.run t (tape.take 3)).isNone do
    throw (IO.userError "the tied selection accepted a short tape")
  IO.println s!"PASS earlier tied row and sample retained on four draws, modeled charge {paid}"

def main (arguments : List String) : IO Unit := do
  zeroSource
  let plan : PhysicalCoverReader.Plan 3 := .covers [BinaryFractionalRows.decodeRow input.costs]
  positive .mass "one-row mass" plan
  positive .size "one-row size" plan
  ties
  if arguments.contains "--positive" then physical
