import DirectedFlowCutGap.BinaryAmplificationPreparation
import DirectedFlowCutGap.PhysicalIntegerRounding

open DirectedFlowCutGap
open BinaryArithmetic RetainedGridState
open ImmutableReferenceSimulation

private def requestThenStop : Program 2 :=
  fun pc => if pc.val = 0 then .request .r0 1 else .halt

def main : IO Unit := do
  let q : BinaryRational.Fraction := ⟨[true,true,false,false],[false,true,false],by decide⟩
  let adj : PairFlags 2 := #v[#v[false,false],#v[false,false]]
  let D : BinaryFractionalGuesses.Input 2 := ⟨adj,[],#v[q,BinaryRational.one]⟩
  let G := BinaryFractionalGuesses.decodeInput D
  let quiet := BinaryAmplificationPreparation.prepare D.costs 0 4 5
  let active := BinaryAmplificationPreparation.prepare D.costs 100 4 5
  unless quiet.trials == 6 && quiet.trials == ChargedPhysicalVertexSolver.trialLimit G 0 4 5 &&
      active.trials == ChargedPhysicalVertexSolver.trialLimit G 100 4 5 && active.trials > quiet.trials &&
      active.costs[0].num == 3 && active.costs[0].den == 2 && 0 < active.paid do
    throw (IO.userError "binary amplifier setup disagrees with the trial size or padded price")
  IO.println s!"PASS zero-call trial cap {quiet.trials}, positive cap {active.trials}, exact padded 3/2, paid {active.paid}"
  let prepared := PhysicalIntegerRounding.boundaryWords 2 2 3
  unless prepared.dimension == (2:ℕ).bits && prepared.level == (2:ℕ).bits && prepared.trials == (3:ℕ).bits &&
      0 < prepared.paid && (PhysicalIntegerRounding.fromWord 3 [true]).toList == [true,false,false] do
    throw (IO.userError "packed boundary words or array mask differ")
  let tape : Bits := [true,false,true]
  let entry : BitState 2 := ⟨[],[],⟨[],[],[],[]⟩,[],0,tape⟩
  let out := CachedGuardedReferenceExecution.execute requestThenStop 2
    (CachedReferenceExecution.FastState.ofReference entry) 0
  let ref := GuardedReferenceExecution.execute requestThenStop 2 entry 0
  let exhausted := CachedGuardedReferenceExecution.execute requestThenStop 2
    (CachedReferenceExecution.FastState.ofReference { entry with source := [] }) 0
  let some (finish,work) := out | throw (IO.userError "cached instruction did not finish")
  unless decide (some (finish.freeze,work) = ref) && finish.source == [false,true] &&
      exhausted.isNone && 0 < work do
    throw (IO.userError "cached guard differs in state, exhaustion, or charge")
  IO.println s!"PASS cached guarded instruction retained its unread tape, exact reference charge {work}, and rejected exhaustion"
  let empty : PairFlags 0 := #v[]
  let some result := PhysicalIntegerRounding.hardRun 0 empty 1 tape |
    throw (IO.userError "direct packed rounding did not finish")
  unless result.mask.toList == [] && result.suffix == tape && 0 < result.paid do
    throw (IO.userError "direct packed rounding lost the mask, suffix or boundary charge")
  IO.println s!"PASS direct packed rounding returns its array mask and entire suffix, paid {result.paid}"
