import DirectedFlowCutGap.EncodedEdgeRounding

open DirectedFlowCutGap
open RawNonnegativeRational

private def weights (w : Code) : Vector (Vector Code 2) 2 :=
  #v[#v[Code.ofNat 3, w], #v[Code.ofNat 4, Code.ofNat 5]]

private def oneEdge (w : Code) : EncodedEdgeGadget.Input 2 :=
  ⟨#v[#v[false, true], #v[false, false]], weights w, weights (Code.ofNat 7)⟩

private def zeroBit (n : ℕ) (hp : 0 < n) : Id (Fin n) := pure ⟨0, hp⟩

def main : IO Unit := do
  let D := oneEdge Code.one
  unless (EncodedEdgeGadget.build D).size == 6 do
    throw (IO.userError "dyadic preparation did not retain exactly four ports and two labels")
  let mass : RetainedGridState.PairFlags 2 :=
    FiniteDrawTrees.execute zeroBit (EncodedEdgeRounding.massBitTree 2 D)
  let size : RetainedGridState.PairFlags 2 :=
    FiniteDrawTrees.execute zeroBit (EncodedEdgeRounding.sizeBitTree 2 D)
  unless mass.toList == [#v[false, true], #v[false, false]] && mass == size do
    throw (IO.userError "dyadic output missed the required edge or returned a nonedge")
  let tiny := oneEdge (Code.one.div (Code.ofNat 8))
  let negligible : RetainedGridState.PairFlags 2 :=
    FiniteDrawTrees.execute zeroBit (EncodedEdgeRounding.massBitTree 2 tiny)
  unless negligible.toList == [#v[false, false], #v[false, false]] do
    throw (IO.userError "tiny-edge fixture did not take the zero-objective branch")
  IO.println "PASS dyadic edge rounding: active gadget, both modes, and tiny input"
