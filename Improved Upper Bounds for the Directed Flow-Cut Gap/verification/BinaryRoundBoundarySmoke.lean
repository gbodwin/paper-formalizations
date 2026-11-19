import DirectedFlowCutGap.BinaryAmplificationPreparation
import DirectedFlowCutGap.PhysicalIntegerRounding

open DirectedFlowCutGap
open BinaryArithmetic RetainedGridState

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
  let some result := PhysicalIntegerRounding.hardRun 3 adj 2 tape |
    throw (IO.userError "direct packed rounding did not finish")
  unless result.mask.toList == [false,false] && result.suffix == tape && prepared.paid < result.paid do
    throw (IO.userError "direct packed rounding lost the mask, suffix or boundary charge")
  IO.println s!"PASS direct packed rounding returns its array mask and entire suffix, paid {result.paid}"
