import DirectedFlowCutGap.EncodedVertexSolver

open DirectedFlowCutGap
open EncodedVertexSolver RawNonnegativeRational

private def path : RetainedGridState.PairFlags 3 :=
  #v[#v[false, true, false], #v[false, false, true], #v[false, false, false]]

private def zeroBit (n : ℕ) (hn : 0 < n) : Id (Fin n) := pure ⟨0, hn⟩

private def checkCut (t : FiniteDrawTrees.Tree (Output 3)) : IO Unit := do
  match FiniteDrawTrees.execute zeroBit t with
  | .cut mask =>
    unless mask[1] do
      throw (IO.userError "the returned cut missed the only internal vertex")
  | _ => throw (IO.userError "expected a feasible cut")

def main : IO Unit := do
  let costs := #v[Code.ofNat 3, Code.ofNat 7, Code.ofNat 5]
  let positive : GraphInput 3 := ⟨path, [(0, 2)], costs⟩
  let zero : GraphInput 3 := ⟨path, [(0, 2)], #v[Code.one, Code.zero, Code.one]⟩
  let impossible : GraphInput 3 := ⟨path, [(0, 1)], costs⟩
  checkCut (massBitTree 2 positive)
  checkCut (sizeBitTree 2 positive)
  checkCut (massBitTree 2 zero)
  match FiniteDrawTrees.execute zeroBit (sizeBitTree 2 impossible) with
  | .infeasible (s, t) =>
    unless s == 0 && t == 1 do
      throw (IO.userError "infeasible output lost the original demand")
  | _ => throw (IO.userError "a direct-edge demand was accepted")
  IO.println "PASS rational vertex solver: both positive rounding laws, zero objective, and infeasible demand"
