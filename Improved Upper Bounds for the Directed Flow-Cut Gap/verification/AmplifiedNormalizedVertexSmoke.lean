import DirectedFlowCutGap.AmplifiedNormalizedVertexSparsest

open DirectedFlowCutGap
open scoped NNRat

private def fraction (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat q)).1

private def line : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def prices : BinaryFractionalRows.Row 3 := #v[fraction 7,fraction (3/2),fraction 9]
private def free : BinaryFractionalRows.Row 3 := #v[fraction 7,fraction 0,fraction 9]
private def across : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]
private def endpoints : RetainedGridState.Flags 3 := #v[true,false,true]
private def internal : RetainedGridState.Flags 3 := #v[false,true,false]
private def costly : RetainedGridState.Flags 3 := #v[true,true,true]
private def tape := [true,false,true]

def main : IO Unit := do
  let score := RationalVertexSparsityCode.score line prices across
  unless RationalVertexSparsityCode.count line across endpoints == 0 &&
      RationalVertexSparsityCode.count line across internal == 1 &&
      (score internal).value == 3/2 && (score costly).value == 35/2 do
    throw (IO.userError "the exact vertex mask score charged endpoints as separating vertices")
  IO.println "PASS endpoint flags alone separated zero pairs and the internal mask scored 3/2"
  let some (q,mask,suffix) := AmplifiedNormalizedVertexSparsest.run line prices across 2 3 tape |
    throw (IO.userError "the amplified vertex optimum returned no cut")
  unless q == 3/2 && mask == internal && suffix == tape do
    throw (IO.userError "the amplified vertex optimum changed the minimum, cut or suffix")
  IO.println "PASS the repeated normalized vertex solver retained optimum 3/2, internal cut and unread tape"
  let some (zero,freeMask,freeTail) := AmplifiedNormalizedVertexSparsest.run line free across 2 3 tape |
    throw (IO.userError "the amplified zero-cost vertex optimum returned no cut")
  unless zero == 0 && freeMask == internal && freeTail == tape &&
      (RationalVertexSparsityCode.score line free across freeMask).value == 0 do
    throw (IO.userError "the amplified free branch changed the original cut, price or suffix")
  IO.println "PASS the amplified free branch selected the same original cut at price zero"
  let samples := FiniteDrawTrees.map (fun i : Fin 3 => if i.val == 0 then internal
    else if i.val == 1 then internal else costly) (FiniteDrawTrees.pick 3 (by decide))
  let tree := EncodedAmplification.bitTree score samples 1 1 2
  let some (winner,rest,used) := EncodedSolverBits.run tree [true,true,false,true,true,false,false] |
    throw (IO.userError "two scored vertex samples did not complete")
  unless winner == internal && rest == [false] && used == 6 do
    throw (IO.userError "scored vertex rejection changed the selected cut or the literal suffix")
  IO.println "PASS bounded rejection used six bits and kept the vertex score 3/2 over 35/2, leaving [false]"
