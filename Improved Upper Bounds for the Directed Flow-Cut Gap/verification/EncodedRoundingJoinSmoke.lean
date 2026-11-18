import DirectedFlowCutGap.EncodedWeightedRounding

open DirectedFlowCutGap
open EncodedUnitCostReplication RetainedGridState RawNonnegativeRational

private def path : PairFlags 3 :=
  #v[#v[false, true, false], #v[false, false, true], #v[false, false, false]]

private def instanceAt (weight cost : Code) : Input 3 :=
  ⟨path, #v[Code.zero, weight, Code.zero], #v[Code.zero, cost, Code.zero]⟩

private def zeroBit (n : ℕ) (hn : 0 < n) : StateM ℕ (Fin n) := do
  modify (· + 1)
  pure ⟨0, hn⟩

private def runMask (s : FiniteDrawTrees.Tree (Flags 3)) : Flags 3 × ℕ :=
  (FiniteDrawTrees.execute zeroBit s).run 0

def main : IO Unit := do
  let (easy, easyCalls) := runMask (EncodedIntegerRounding.bitTree 2 path 1 (by decide))
  let (long, longCalls) := runMask (EncodedIntegerRounding.bitTree 2 path (10 ^ 120) (by decide))
  unless easy.toArray == #[true, true, true] && easyCalls == 0 &&
      long.toArray == #[false, false, false] && longCalls == 0 do
    throw (IO.userError "integer threshold dispatch did not return both expected masks")
  let (small, smallCalls) := runMask (EncodedUniformRounding.bitTree 2 (instanceAt Code.zero Code.one))
  let (uniform, uniformCalls) := runMask (EncodedUniformRounding.bitTree 2 (instanceAt Code.one Code.one))
  unless small.toArray == #[false, false, false] && smallCalls == 0 &&
      uniform[1] && uniformCalls == 0 do
    throw (IO.userError "uniform chain dispatch lost its trivial branch or original middle vertex")
  let (zeroCost, zeroCalls) :=
    runMask (EncodedWeightedRounding.bitTree 2 (instanceAt Code.one Code.zero))
  let (weighted, weightedCalls) :=
    runMask (EncodedWeightedRounding.bitTree 2 (instanceAt Code.one (Code.ofNat 7)))
  unless zeroCost.toArray == #[false, true, false] && zeroCalls == 0 &&
      weighted[1] && weightedCalls == 0 do
    throw (IO.userError "weighted dispatch lost its zero or positive objective branch")
  IO.println "PASS rounding joins: small and huge thresholds, uniformization, and both cost branches"
