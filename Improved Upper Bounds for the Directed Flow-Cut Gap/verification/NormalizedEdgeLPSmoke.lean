import DirectedFlowCutGap.NormalizedEdgeLPRound
import DirectedFlowCutGap.RationalSparsestFairTape

open DirectedFlowCutGap
open scoped NNRat
open BinaryArithmetic (Bits)
open BinaryRational (Fraction zero)

private def adjacency : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def price : Fraction := ⟨[true,true],[false,true],by decide⟩
private def prices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,price],#v[zero,zero]]
private def zeroPrices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,zero],#v[zero,zero]]
private def pairs : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private def tape : Bits := [true,false,true]

def main : IO Unit := do
  let below := NormalizedEdgeLP.findWeights adjacency prices pairs.get 1 1
  let some atBudget := NormalizedEdgeLP.findWeights adjacency prices pairs.get 1 (3/2) |
    throw (IO.userError "feasibility rejected the exact rational price")
  let some (optimum,optimalWeights) := NormalizedEdgeLP.minimize adjacency prices pairs.get 1 |
    throw (IO.userError "the rational objective could not find the finite optimum")
  let c := (BinaryRational.decode (atBudget[0][1])).value
  let d := (BinaryRational.decode (optimalWeights[0][1])).value
  let rows := (NormalizedEdgeLP.rows adjacency prices pairs.get 1 1).length
  unless below.isNone && c == 1 && d == 1 && optimum == (3/2 : ℚ) && rows == 10 do
    throw (IO.userError "the cost budget, rational optimum or feasible edge weight changed")
  IO.println s!"PASS {rows} exact linear rows rejected budget one, accepted budget three halves, and independently minimized to {optimum} with unit arc length"
  let some (q,.cut mask rest) := NormalizedEdgeLPRound.runOptimal adjacency prices pairs .size 0 tape |
    throw (IO.userError "the original optimum was not rounded")
  let some (massQ,.cut massMask massRest) :=
    NormalizedEdgeLPRound.runOptimal adjacency prices pairs .mass 0 tape |
    throw (IO.userError "the mass round rejected the original optimum")
  unless q == optimum && (mask.toList.map Vector.toList) == [[false,true],[false,false]] &&
      rest == tape && massQ == q && massMask == mask && massRest == tape do
    throw (IO.userError "the optimum or reached literal-tape cut changed")
  IO.println s!"PASS both literal-tape modes rounded optimum {q} to the original cut {mask.toList.map Vector.toList}, preserving {rest}"
  let some (q0,.cut zeroMask zeroRest) :=
    NormalizedEdgeLPRound.runOptimal adjacency zeroPrices pairs .mass 0 tape |
    throw (IO.userError "the zero objective failed to produce a valid cut")
  unless q0 == 0 && zeroMask == mask && zeroRest == tape do
    throw (IO.userError "the zero optimum or its original cut changed")
  let self : Vector (Fin 2 × Fin 2) 1 := #v[(0,0)]
  unless (NormalizedEdgeLP.minimize adjacency prices self.get 1).isNone do
    throw (IO.userError "the empty self path cannot satisfy positive normalization")
  IO.println "PASS zero edge price still yielded the original cut and unread tape, while positive normalization of a sole self demand was infeasible"
