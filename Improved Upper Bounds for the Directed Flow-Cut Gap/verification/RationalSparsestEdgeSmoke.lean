import DirectedFlowCutGap.RationalSparsestEdgeRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryArithmetic (Bits)
open BinaryRational (Fraction zero one)

private def half : Fraction := ⟨[true],[false,true],by decide⟩
private def adjacency : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def weights : RationalEdgeThresholds.Weights 2 := #v[#v[zero,half],#v[zero,zero]]
private def prices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[zero,zero]]
private def forward : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private def reverse : Vector (Fin 2 × Fin 2) 2 := #v[(0,1),(1,0)]
private def self : Vector (Fin 2 × Fin 2) 1 := #v[(0,0)]

private def choose : IO Unit := do
  let .threshold i τ := RationalSparsestEdgeThreshold.choose adjacency weights forward |
    throw (IO.userError "the reachable positive distance was not selected")
  let normalized := RationalSparsestEdgeRound.scaled adjacency weights prices τ
  let .unreachable j := RationalSparsestEdgeThreshold.choose adjacency weights reverse |
    throw (IO.userError "the unreachable original demand was treated as finite")
  let .zero := RationalSparsestEdgeThreshold.choose adjacency weights self |
    throw (IO.userError "a zero-length self-path selected a nonzero threshold")
  unless i.val == 0 && (τ : ℚ) == 1/2 && j.val == 1 &&
      normalized.weights[0][1].value == 1 && normalized.costs[0][1].value == 1 do
    throw (IO.userError "exact rational distance, threshold or scaling changed")
  let ties (x : Fin 3) : ℚ≥0 := if x.val=2 then 1/2 else 1
  let some k := RationalHarmonicThreshold.choose ties |
    throw (IO.userError "the finite tie case failed to select a distance")
  unless k.val != 2 && RationalHarmonicThreshold.count ties (ties k) == 2 do
    throw (IO.userError "equal distances did not both count at the threshold")
  IO.println s!"PASS exact rational threshold {(τ : ℚ)} from demand {i.val}, tied count 2, unit scaled length and price, unreachable demand {j.val}, finite self-distance zero"

private def tape : Bits := [true,false,true]

private def runRounds : IO Unit := do
  let some (.cut empty keep) := RationalSparsestEdgeRound.run adjacency weights prices reverse .mass 0 tape |
    throw (IO.userError "the unreachable branch did not return the empty cut")
  let some .zeroDistance := RationalSparsestEdgeRound.run adjacency weights prices self .mass 0 tape |
    throw (IO.userError "finite zero distance did not retain its distinct result")
  unless (empty.toList.map Vector.toList) == [[false,false],[false,false]] && keep == tape do
    throw (IO.userError "the unreachable branch consumed tape or cut an arc")
  let positive := [ChargedVertexModes.Mode.mass,ChargedVertexModes.Mode.size].map
    fun mode => RationalSparsestEdgeRound.run adjacency weights prices forward mode 0 tape
  for output in positive do
    let some (.cut chosen rest) := output |
      throw (IO.userError "the reached one-arc round did not return a cut")
    unless (chosen.toList.map Vector.toList) == [[false,true],[false,false]] && rest == tape do
      throw (IO.userError "the reached round changed the one-arc cut or unread tape")
  IO.println s!"PASS both literal-tape modes cut the positive original arc after scaling, while the unreachable case cut nothing and all three cuts kept {tape}"

def main : IO Unit := do
  choose
  runRounds
