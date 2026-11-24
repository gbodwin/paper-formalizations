import DirectedFlowCutGap.RationalSparsestVertexRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (Fraction zero one)

private def half : Fraction := ⟨[true],[false,true],by decide⟩
private def A : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def withEndpoints : BinaryFractionalRows.Row 3 := #v[one,half,one]
private def lengths : BinaryFractionalRows.Row 3 := #v[zero,half,zero]
private def prices : BinaryFractionalRows.Row 3 := #v[one,one,one]
private def demand : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]
private def tape := [true,false,true]

def main : IO Unit := do
  let d := RationalSparsestVertexDistances.distance A withEndpoints (0,2)
  let direct := RationalSparsestVertexDistances.distance A withEndpoints (0,1)
  let self := RationalSparsestVertexDistances.distance A withEndpoints (1,1)
  unless d == some (1/2) && direct == some 0 && self == some 0 do
    throw (IO.userError "the vertex distances counted a demand endpoint")
  let .threshold i τ := RationalSparsestVertexThreshold.choose A withEndpoints demand |
    throw (IO.userError "the positive internal threshold was not found")
  unless i.val == 0 && τ == 1/2 do
    throw (IO.userError "the harmonic vertex threshold changed")
  IO.println "PASS endpoint weights were ignored, giving distance and threshold 1/2, and direct/self distance zero"
  let some (.cut m massTape) := RationalSparsestVertexRound.run A lengths prices demand .mass 0 tape |
    throw (IO.userError "positive vertex mass mode did not produce a cut")
  let some (.cut s sizeTape) := RationalSparsestVertexRound.run A lengths prices demand .size 0 tape |
    throw (IO.userError "positive vertex size mode did not produce a cut")
  unless m.toList == [false,true,false] && s == m && massTape == tape && sizeTape == tape do
    throw (IO.userError "the vertex modes changed the original internal cut or unread tape")
  IO.println s!"PASS both vertex modes cut the original internal vertex {m.toList} with unread tape {massTape}"
  let some (.cut empty rest) :=
    RationalSparsestVertexRound.run A lengths prices (#v[(2,0)]) .size 0 tape |
    throw (IO.userError "the unreachable vertex demand did not give the empty cut")
  let some .zeroDistance := RationalSparsestVertexRound.run A lengths prices (#v[(0,1)]) .mass 0 tape |
    throw (IO.userError "the finite zero vertex demand was not distinguished")
  unless empty.toList == [false,false,false] && rest == tape do
    throw (IO.userError "the unreachable vertex case changed the tape")
  IO.println "PASS unreachable vertex demand returned the empty cut without reads and finite zero had its own result"
