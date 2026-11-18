import DirectedFlowCutGap.EncodedEdgeSolver

open DirectedFlowCutGap RawNonnegativeRational

private def instanceAt (cost : Code) (demand : Fin 2 × Fin 2) : EncodedEdgeLineInput.Input 2 :=
  ⟨#v[#v[false, true], #v[false, false]], [demand, demand],
    #v[#v[Code.ofNat 101, cost], #v[Code.ofNat 103, Code.ofNat 107]]⟩

private def zeroBit (n : ℕ) (hp : 0 < n) : Id (Fin n) := pure ⟨0, hp⟩

private def checkCut (mode : EncodedEdgeSolver.Mode) (c : Code) : IO Unit := do
  match FiniteDrawTrees.execute zeroBit (EncodedEdgeSolver.bitTree 0 (instanceAt c (0, 1)) mode) with
  | .cut mask =>
    unless mask.toList == [#v[false, true], #v[false, false]] do
      throw (IO.userError "edge solver missed the direct demand or selected a nonedge")
  | _ => throw (IO.userError "feasible edge instance returned no cut")

def main : IO Unit := do
  checkCut EncodedEdgeSolver.massMode Code.one
  checkCut EncodedEdgeSolver.sizeMode Code.one
  checkCut EncodedEdgeSolver.massMode Code.zero
  match FiniteDrawTrees.execute zeroBit
      (EncodedEdgeSolver.bitTree 0 (instanceAt Code.one (0, 0)) EncodedEdgeSolver.sizeMode) with
  | .infeasible (some (s, t)) =>
    unless s.val == 0 && t.val == 0 do
      throw (IO.userError "edge self-demand witness changed")
  | _ => throw (IO.userError "length-zero edge demand should be infeasible")
  IO.println "PASS rational edge solver: both modes, zero cost, original edges, and self-demand witness"
