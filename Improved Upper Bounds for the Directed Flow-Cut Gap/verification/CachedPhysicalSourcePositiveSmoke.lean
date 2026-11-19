import DirectedFlowCutGap.CachedReferenceExecution
import DirectedFlowCutGap.PhysicalVertexSolver
import FinalDispatchPositiveFixtureSupport

open DirectedFlowCutGap
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution FinalDispatchPositiveFixture

private structure Trace where
  state : FastState 13384
  instructions : ℕ
  charge : ℕ
  terminalCharge : ℕ
  events : List Event
  visits : Visits

private def run (cap : ℕ) (start : FastState 13384) : IO Trace :=
  go cap start 0 0 [] {}
where
  go : ℕ → FastState 13384 → ℕ → ℕ → List Event → Visits → IO Trace
  | 0, s, i, q, _, visits =>
    throw (IO.userError ("physical attempt cap exhausted at " ++ toString i ++
      " successful instructions and " ++ toString q ++ " operations, pc=" ++ toString s.pc.val ++
      ", records=" ++ toString s.store.cells.size ++ ", visits=" ++ reprStr visits))
  | fuel + 1, s, i, q, events, visits => do
    let seen := if 64 ≤ s.pc.val then visits.observe (s.pc.val - 64) else visits
    match CachedReferenceExecution.attempt PhysicalSourceDispatch.program s with
    | .stopped state charge => return ⟨state, i, q + charge, charge, events.reverse, seen⟩
    | .completed r =>
      let total := q + r.cost
      let i' := i + 1
      if i' % 100000 == 0 then
        IO.println ("CACHED_PHYSICAL_PROGRESS instructions=" ++ toString i' ++
          " pc=" ++ toString r.state.pc.val ++ " heap=" ++ toString r.state.store.cells.size ++
          " operations=" ++ toString total)
        (← IO.getStdout).flush
      go fuel r.state i' total (r.events.reverse ++ events) seen

private def roundCover (plan : PhysicalCoverReader.Plan 3) (physical : ℕ)
    (round : EncodedVertexSolver.Rounding 3) : IO ℕ := do
  let graph := BinaryFractionalGuesses.decodeInput input
  let confidence := EncodedVertexAmplification.confidenceExponent 3 0
  let tape := [true, false, false, true]
  let some (tree, paid) := PhysicalVertexSolver.boundedFromRun
    (EncodedVertexAmplification.roundDrawBound 3) confidence (confidence + 1)
    graph round (some (plan, physical))
      | throw (IO.userError "the physical plan did not initialize rounding")
  match EncodedSolverBits.run tree tape with
  | some (.cut mask, rest, used) =>
    unless mask[1] && paid == physical && rest == tape.drop used do
      throw (IO.userError "rounding lost the internal vertex, paid prefix, or original tape suffix")
    return used
  | _ => throw (IO.userError "rounding the actual positive plan did not produce a cut")

def main (args : List String) : IO Unit := do
  let cap ← parseCap args
  preflight
  let source := PhysicalSourceDispatch.input input
  let start := FastState.ofReference (PhysicalSourceDispatch.initial source)
  IO.println ("BEGIN cached physical source trace cap=" ++ toString cap ++ " sourceBits=" ++ toString source.length)
  (← IO.getStdout).flush
  let result ← run cap start
  IO.println ("CACHED_PHYSICAL_STOPPED instructions=" ++ toString result.instructions ++
    " heap=" ++ toString result.state.store.cells.size ++ " operations=" ++ toString result.charge)
  (← IO.getStdout).flush
  unless result.state.pc == PhysicalSourceDispatch.solveLabel 13319 && result.visits.complete &&
      result.state.stack.isEmpty && result.state.source.isEmpty &&
      result.events == source.map Event.request && result.terminalCharge == controlCost 13384 &&
      result.instructions ≤ PhysicalSourceDispatch.steps input &&
      result.charge ≤ PhysicalSourceDispatch.paidBound input do
    throw (IO.userError ("positive source trace failed its terminal, events, or bound check, visits=" ++
      reprStr result.visits))
  let out := eraseState result.state.freeze
  unless out.next == out.heap.length &&
      readTable out.heap (out.heap.length + 1) out.registers.a == some costFields &&
      readMatrix out.heap (out.heap.length + 1) out.registers.b == some rows &&
      readTable out.heap (out.heap.length + 1) out.registers.c == some demandFields do
    throw (IO.userError "physical source trace changed the original roots")
  let states ← expectedStates
  unless states.length == 9 && readCovers out.heap out.registers.d == some states do
    throw (IO.userError "positive source trace changed the ordered fractional output")
  let some plan := PhysicalCoverReader.readPlan 3 out.heap out.registers.d
    | throw (IO.userError "could not read the positive physical output for rounding")
  let massReads ← roundCover plan result.charge EncodedWeightedRounding.tree
  let sizeReads ← roundCover plan result.charge EncodedSizeRounding.tree
  IO.println ("PASS cached physical source: orderedStates=" ++ toString states.length ++
    " sourceRequests=" ++ toString result.events.length ++ " instructions=" ++
    toString result.instructions ++ " paidOperations=" ++ toString result.charge ++
    " terminalOperations=" ++ toString result.terminalCharge ++
    " massRandomReads=" ++ toString massReads ++ " sizeRandomReads=" ++ toString sizeReads)
