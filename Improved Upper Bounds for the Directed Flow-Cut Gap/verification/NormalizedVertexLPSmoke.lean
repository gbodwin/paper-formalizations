import DirectedFlowCutGap.NormalizedVertexLPZero

open DirectedFlowCutGap
open scoped NNRat

private def fraction (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat q)).1

private def line : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def prices : BinaryFractionalRows.Row 3 := #v[fraction 7, fraction (3/2), fraction 9]
private def free : BinaryFractionalRows.Row 3 := #v[fraction 7, fraction 0, fraction 9]
private def across : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]
private def immediate : Vector (Fin 3 × Fin 3) 1 := #v[(0,1)]
private def self : Vector (Fin 3 × Fin 3) 1 := #v[(1,1)]
private def tape := [true,false,true]

def main : IO Unit := do
  let some (q,lengths) := NormalizedVertexLP.minimize line prices across.get 1 |
    throw (IO.userError "the endpoint-excluding LP had no feasible assignment on a two-edge path")
  unless q == 3/2 && (BinaryRational.decode lengths[0]).value == 0 &&
      (BinaryRational.decode lengths[1]).value == 1 &&
      (BinaryRational.decode lengths[2]).value == 0 do
    throw (IO.userError "the LP charged a path endpoint or returned the wrong internal length")
  IO.println "PASS the exact vertex LP attained 3/2 with internal length 1 and endpoint lengths 0"
  let some (optimum,.cut mask suffix) := NormalizedVertexLPRound.run line prices across 0 tape |
    throw (IO.userError "the selected vertex round returned no cut")
  unless optimum == q && mask.toList == [false,true,false] && suffix == tape do
    throw (IO.userError "the selected vertex round changed the optimum, original cut, or unread suffix")
  IO.println "PASS the computed vertex optimum rounded to the original internal cut and preserved [true, false, true]"
  let some (zero,.cut freeMask freeSuffix) := NormalizedVertexLPRound.run line free across 0 tape |
    throw (IO.userError "the zero-optimum vertex instance returned no cut")
  unless zero == 0 && freeMask == mask && freeSuffix == tape &&
      (NormalizedVertexLP.minimize line prices immediate.get 1).isNone &&
      (NormalizedVertexLP.minimize line prices self.get 1).isNone do
    throw (IO.userError "zero cut, immediate arc, or self demand was classified incorrectly")
  IO.println "PASS zero price returned the original cut, and positive normalization was infeasible for direct and self demands"
