import FinalDispatchPositiveFixtureSupport

/-! NEW UNRUN NATURAL-REFERENCE DIAGNOSTIC. This uses tickNatural, not the physical
BitState interpreter. A completed diagnostic NEVER establishes a physical run,
bit-operation cost, paid terminal cost, kernel audit or whole-paper result. -/
namespace DirectedFlowCutGap.FinalDispatchPositiveNaturalDiagnostic
open BinaryArithmetic ImmutableReferenceSimulation
open FinalDispatchPositiveFixture

structure Totals where
  attempts : ℕ := 0
  instructions : ℕ := 0
  eventCount : ℕ := 0
  visits : Visits := {}

structure Trace where
  state : NaturalState 13320
  totals : Totals
  halted : Bool

/-- Tail call after progress output; no recursive chunk return retains a heap. -/
def execute (cap : ℕ) (s : NaturalState 13320) : IO Trace := go cap s {}
where
  go : ℕ → NaturalState 13320 → Totals → IO Trace
  | 0,s,t => return ⟨s,t,false⟩
  | remaining+1,s,t => do
      let attempts := t.attempts+1
      let visits := t.visits.observe s.pc.val
      match tickNatural FinalDispatch.program s with
      | none =>
          if attempts % 1000 == 0 then
            IO.println ("NATURAL_DIAGNOSTIC_PROGRESS attempts=" ++ toString attempts ++
              " pc=" ++ toString s.pc.val ++ " heap=" ++ toString s.heap.length ++ " halted=true")
            (← IO.getStdout).flush
          return ⟨s,{t with attempts := attempts,visits := visits},true⟩
      | some r =>
          let next : Totals := ⟨attempts,t.instructions+1,t.eventCount+r.events.length,visits⟩
          if attempts % 1000 == 0 then
            IO.println ("NATURAL_DIAGNOSTIC_PROGRESS attempts=" ++ toString attempts ++
              " instructions=" ++ toString next.instructions ++ " pc=" ++ toString r.state.pc.val ++
              " heap=" ++ toString r.state.heap.length ++ " visits=" ++ reprStr visits)
            (← IO.getStdout).flush
          go remaining r.state next

def main (args : List String) : IO Unit := do
  let cap ← parseCap args
  IO.println ("BEGIN NATURAL_REFERENCE_DIAGNOSTIC_ONLY maxAttempts=" ++ toString cap)
  (← IO.getStdout).flush
  preflight
  let start := eraseState initial
  unless start.next == start.heap.length && start.heap.length == 56 &&
      checkOriginalRoots start start do
    throw (IO.userError "natural diagnostic input packing failed")
  let actual ← execute cap start
  let t := actual.totals
  unless actual.halted do
    throw (IO.userError ("INCOMPLETE_NATURAL_DIAGNOSTIC cap exhausted; attempts=" ++
      toString t.attempts ++ " pc=" ++ toString actual.state.pc.val ++
      " heap=" ++ toString actual.state.heap.length ++ " visits=" ++ reprStr t.visits))
  IO.println ("NATURAL_DIAGNOSTIC_STOPPED instructions=" ++ toString t.instructions ++
    " pc=" ++ toString actual.state.pc.val ++ " heap=" ++ toString actual.state.heap.length)
  (← IO.getStdout).flush
  unless actual.state.pc == 13319 && t.visits.complete && actual.state.stack.isEmpty &&
      actual.state.source == start.source && t.eventCount == 0 &&
      t.attempts == t.instructions+1 && actual.state.next == actual.state.heap.length &&
      checkOriginalRoots start actual.state do
    throw (IO.userError "FAIL_NATURAL_DIAGNOSTIC route/terminal/input checks")
  let wanted ← expectedStates
  unless wanted.length == 9 && readCovers actual.state.heap actual.state.registers.d == some wanted do
    throw (IO.userError "FAIL_NATURAL_DIAGNOSTIC ordered solveInput state projection")
  IO.println ("NATURAL_DIAGNOSTIC_MATCH_ONLY orderedStates=" ++ toString wanted.length ++
    " instructions=" ++ toString t.instructions ++ " heap=" ++ toString actual.state.heap.length ++
    "; this is not a physical execution or physical-cost verification")
  (← IO.getStdout).flush

end DirectedFlowCutGap.FinalDispatchPositiveNaturalDiagnostic

def main := DirectedFlowCutGap.FinalDispatchPositiveNaturalDiagnostic.main
