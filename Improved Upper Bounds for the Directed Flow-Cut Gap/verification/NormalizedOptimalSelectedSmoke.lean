import DirectedFlowCutGap.NormalizedOptimalSelected

open DirectedFlowCutGap
open scoped NNRat
open BinaryArithmetic (Bits)
open BinaryRational (Fraction zero)

private def one : Fraction := ⟨[true],[true],by decide⟩
private def oneArc : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def bothArcs : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[true,false]]
private def prices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[one,zero]]
private def free : RationalEdgeThresholds.Weights 2 := #v[#v[zero,zero],#v[zero,zero]]
private def oneDemand : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private def bothDemands : Vector (Fin 2 × Fin 2) 2 := #v[(0,1),(1,0)]
private def tape : Bits := [true,false,true]

def main : IO Unit := do
  let some (m, lengths) := NormalizedEdgeLP.minimize oneArc prices oneDemand.get 1 |
    throw (IO.userError "one original arc was infeasible")
  match NormalizedOptimalMode.pick oneArc lengths oneDemand with
  | .size => throw (IO.userError "one positive demand should use the mass scale")
  | .mass => pure ()
  let some (q,.cut mask rest) := NormalizedOptimalMode.runBest oneArc prices oneDemand 0 tape |
    throw (IO.userError "selected mass round failed")
  unless m == 1 && q == m && rest == tape && mask.toList.map Vector.toList == [[false,true],[false,false]] do
    throw (IO.userError "selected mass round changed the price, cut or suffix")
  IO.println s!"PASS selected mass mode found optimum {q}, original arc cut {mask.toList.map Vector.toList}, and unread tape {rest}"
  let some (d, bothLengths) := NormalizedEdgeLP.minimize bothArcs prices bothDemands.get 2 |
    throw (IO.userError "both original arcs were infeasible")
  match NormalizedOptimalMode.pick bothArcs bothLengths bothDemands with
  | .mass => throw (IO.userError "two opposed demands should use the size scale")
  | .size => pure ()
  let some (price,.cut bothMask suffix) := NormalizedOptimalMode.runBest bothArcs prices bothDemands 0 tape |
    throw (IO.userError "selected size round failed")
  unless price == 2 && d == price && suffix == tape && !bothMask[0][0] && !bothMask[1][1] &&
      (bothMask[0][1] || bothMask[1][0]) do
    throw (IO.userError "selected size round changed the price, valid cut or suffix")
  IO.println s!"PASS selected size mode found optimum {price}, original arc cut {bothMask.toList.map Vector.toList}, and unread tape {suffix}"
  let some (q0,.cut zeroMask zeroSuffix) := NormalizedOptimalMode.runBest oneArc free oneDemand 0 tape |
    throw (IO.userError "zero optimal price prevented the selected cut")
  unless q0 == 0 && zeroMask == mask && zeroSuffix == tape do
    throw (IO.userError "selected zero optimum changed the cut or suffix")
  IO.println "PASS selected zero optimum returned the original arc cut and exact unread tape"
