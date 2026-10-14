import FinalDispatchPositiveFixtureSupport

/-! NEW UNRUN positive whole-dispatcher physical fixture. No Lean/compiler has
been invoked for this draft. It literally executes ImmutableReferenceTerminal.attempt
on BitState 13320, including the paid terminal attempt. -/
namespace DirectedFlowCutGap.FinalDispatchPositivePhysicalSmoke
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open FinalDispatchPositiveFixture

structure Totals where
  attempts : ℕ := 0
  instructions : ℕ := 0
  successfulOperations : ℕ := 0
  eventCount : ℕ := 0
  visits : Visits := {}

structure Trace where
  state : BitState 13320
  totals : Totals
  terminalOperations : ℕ
  halted : Bool

/-- Direct tail recursion with one current state and scalar/Boolean totals.
There is no recursive return combining chunks, state list, or saved old heap.
The caller retains only the small ORIGINAL heap for its preservation test. -/
def execute (maxAttempts : ℕ) (s : BitState 13320) : IO Trace :=
  go maxAttempts s {}
where
  go : ℕ → BitState 13320 → Totals → IO Trace
  | 0,s,t => return ⟨s,t,0,false⟩
  | remaining+1,s,t => do
      let a := ImmutableReferenceTerminal.attempt FinalDispatch.program s
      let attempts := t.attempts+1
      let visits := t.visits.observe s.pc.val
      match a.result with
      | none =>
          if attempts % 1000 == 0 then
            IO.println ("PHYSICAL_PROGRESS attempts=" ++ toString attempts ++
              " instructions=" ++ toString t.instructions ++ " pc=" ++ toString s.pc.val ++
              " heap=" ++ toString s.heap.length ++ " halted=true operationsIncludingHalt=" ++
              toString (t.successfulOperations+a.operations))
            (← IO.getStdout).flush
          return ⟨s,{t with attempts := attempts,visits := visits},a.operations,true⟩
      | some r =>
          let next : Totals := ⟨attempts,t.instructions+1,
            t.successfulOperations+a.operations,t.eventCount+r.events.length,visits⟩
          if attempts % 1000 == 0 then
            IO.println ("PHYSICAL_PROGRESS attempts=" ++ toString attempts ++
              " instructions=" ++ toString next.instructions ++ " pc=" ++ toString r.state.pc.val ++
              " heap=" ++ toString r.state.heap.length ++ " successfulOperations=" ++
              toString next.successfulOperations ++ " visits=" ++ reprStr visits)
            (← IO.getStdout).flush
          -- Tail position: never bind this recursive result and then combine it.
          go remaining r.state next

def main (args : List String) : IO Unit := do
  let cap ← parseCap args
  IO.println ("BEGIN PHYSICAL positive full dispatcher; maxAttempts=" ++ toString cap)
  (← IO.getStdout).flush
  preflight
  let start := initial
  let original := eraseState start
  unless value start.next == start.heap.length && start.heap.length == 56 &&
      checkOriginalRoots original original do
    throw (IO.userError "initial original-root packing/dense-cursor check failed")
  let actual ← execute cap start
  let t := actual.totals
  unless actual.halted do
    throw (IO.userError ("INCOMPLETE_PHYSICAL attempt cap exhausted; attempts=" ++
      toString t.attempts ++ " instructions=" ++ toString t.instructions ++
      " pc=" ++ toString actual.state.pc.val ++ " heap=" ++ toString actual.state.heap.length ++
      " successfulOperations=" ++ toString t.successfulOperations ++ " visits=" ++ reprStr t.visits))
  let paid := t.successfulOperations+actual.terminalOperations
  IO.println ("PHYSICAL_STOPPED attempts=" ++ toString t.attempts ++
    " instructions=" ++ toString t.instructions ++ " pc=" ++ toString actual.state.pc.val ++
    " heap=" ++ toString actual.state.heap.length ++ " operationsIncludingHalt=" ++ toString paid ++
    " terminalOperations=" ++ toString actual.terminalOperations)
  (← IO.getStdout).flush
  -- A failed lookup/empty-stack return is not accepted as a successful halt.
  unless actual.state.pc == 13319 && t.visits.complete && actual.state.stack.isEmpty &&
      actual.state.source == start.source && t.eventCount == 0 &&
      t.attempts == t.instructions+1 && actual.terminalOperations == controlCost 13320 &&
      actual.terminalOperations == 13336 do
    throw (IO.userError ("FAIL_PHYSICAL terminal/positive-route checks; visits=" ++ reprStr t.visits))
  let finish := eraseState actual.state
  unless actual.state.registers.a == start.registers.a &&
      actual.state.registers.b == start.registers.b && actual.state.registers.c == start.registers.c &&
      actual.state.heap.take start.heap.length == start.heap &&
      value actual.state.next == actual.state.heap.length && checkOriginalRoots original finish do
    throw (IO.userError "FAIL_PHYSICAL original-root/raw-prefix/dense-cursor checks")
  let terminal := ImmutableReferenceTerminal.attempt FinalDispatch.program actual.state
  unless terminal.result.isNone && terminal.operations == actual.terminalOperations do
    throw (IO.userError "FAIL_PHYSICAL terminal replay disagrees")
  -- Replay is a test observation; it is NOT counted as another execution attempt.
  IO.println "PHYSICAL_VERIFY comparing ordered output with high-level solveInput"
  (← IO.getStdout).flush
  let wanted ← expectedStates
  let decoded := readCovers finish.heap finish.registers.d
  unless wanted.length == 9 && decoded == some wanted do
    throw (IO.userError "FAIL_PHYSICAL exact ordered solveInput state projection differs")
  let bound := FinalDispatch.inputBound adjacency costs demands
  unless t.instructions ≤ bound && paid ≤
      completeBound 13320 (start.heap.length+1) (start.heap.length+1) bound do
    throw (IO.userError "FAIL_PHYSICAL instruction/complete physical operation bound")
  IO.println ("PASS_PHYSICAL positive full dispatcher; orderedStates=" ++ toString wanted.length ++
    " attempts=" ++ toString t.attempts ++ " instructions=" ++ toString t.instructions ++
    " operationsIncludingHalt=" ++ toString paid ++ " terminalOperations=" ++
    toString actual.terminalOperations ++ " finalHeap=" ++ toString actual.state.heap.length)
  (← IO.getStdout).flush

end DirectedFlowCutGap.FinalDispatchPositivePhysicalSmoke

def main := DirectedFlowCutGap.FinalDispatchPositivePhysicalSmoke.main
