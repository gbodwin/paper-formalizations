import DirectedFlowCutGap.BinaryIntegerCutoff

open DirectedFlowCutGap
open BinaryArithmetic RetainedGridState

private def check (n L : ℕ) (inside hard : Bool) : IO Unit := do
  let gate := BinaryIntegerCutoff.compute n L
  let legacy := EncodedEpochParameters.compute n
  unless gate.inside == inside && gate.hard == hard && gate.parameters.restart == legacy.restart &&
      gate.parameters.fuel == legacy.fuel && gate.parameters.cap == legacy.cap &&
      gate.parameters.work == legacy.work && 0 < gate.paid && gate.paid ≤ BinaryIntegerCutoff.budget n L.size do
    throw (IO.userError s!"binary cutoff differs at n={n}, L={L}")

private def fallback (L : ℕ) (expected : Bits) : IO Unit := do
  let adj : PairFlags 2 := #v[#v[false,true],#v[false,false]]
  let tape : Bits := [true,false,true]
  let some (r,arithmetic) := BinaryIntegerCutoff.run 3 adj L tape |
    throw (IO.userError "integer cutoff fallback exhausted the tape")
  let some legacy := PhysicalIntegerRounding.run 3 adj L tape |
    throw (IO.userError "retained integer fallback exhausted the tape")
  unless r.mask.toList == expected && r.mask.toList == legacy.mask.toList &&
      r.suffix == tape && r.suffix == legacy.suffix && r.paid == legacy.paid && 0 < arithmetic do
    throw (IO.userError "binary cutoff changed a retained fallback")

def main : IO Unit := do
  check 0 0 true false
  check 2 3 false false
  fallback 3 [false,false]
  fallback 2 [true,true]
  IO.println "PASS both integer fallback masks, their exact tape and retained operation counts"
  let n := 2 ^ 128
  check n n true true
  check n 1 true false
  check n (n+1) false false
  IO.println "PASS binary cap and cube predicates at 129-bit dimensions with exact epoch parameters"
