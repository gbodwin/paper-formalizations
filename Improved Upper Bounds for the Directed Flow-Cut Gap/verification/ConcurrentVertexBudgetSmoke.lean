import DirectedFlowCutGap.ConcurrentVertexBudgetRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (one)

private def fraction (q : ℚ≥0) : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat q)).1
private def line : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def chain : BinaryFractionalWalkOracle.Adjacency 4 :=
  #v[#v[false,true,false,false],#v[false,false,true,false],#v[false,false,false,true],#v[false,false,false,false]]
private def positive : BinaryFractionalRows.Row 3 := #v[fraction 7,fraction (3/2),fraction 9]
private def free : BinaryFractionalRows.Row 3 := #v[fraction 7,fraction 0,fraction 9]
private def unit : BinaryFractionalRows.Row 4 := #v[one,one,one,one]
private def across : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]
private def several : Vector (Fin 4 × Fin 4) 3 := #v[(0,2),(1,3),(0,3)]
private def tape := List.replicate 16384 false ++ [true,false,true]

def main : IO Unit := do
  let row : FractionalCover.Row 4 := #v[1,1,1,1]
  let pivot := ConcurrentVertexOracle.oracle (by decide) chain several row row
  unless pivot.column.toList == [0,2,2,0] && (pivot.pivot.val == 1 || pivot.pivot.val == 2) do
    throw (IO.userError "the joint column did not preserve the repeated internal vertices")
  IO.println s!"PASS the original three vertex paths produced column {pivot.column.toList} and positive pivot {pivot.pivot.val}"
  let some small := ConcurrentVertexBudgetSelection.choose (by decide) line positive across |
    throw (IO.userError "the cost-and-mass grid did not return a plan on the short path")
  match small.mode with
  | .size => throw (IO.userError "the short-path fixture did not choose the mass mode")
  | .mass => pure ()
  let some (mask,rest) := ConcurrentVertexBudgetRound.run (by decide) line positive across 2 3 tape |
    throw (IO.userError "the budget-selected vertex mass trial did not return a cut")
  unless mask.toList == [false,true,false] && rest == tape.drop (tape.length-rest.length) do
    throw (IO.userError "the vertex mass trial used the wrong cut or suffix")
  IO.println s!"PASS the generated vertex mass plan rounded the original internal vertex at score {(small.receipt : ℚ)}"
  let some large := ConcurrentVertexBudgetSelection.choose (by decide) chain unit several |
    throw (IO.userError "the cost-and-mass grid did not return a plan on the chain")
  match large.mode with
  | .mass => throw (IO.userError "the chain fixture did not choose the size mode")
  | .size => pure ()
  let some (sizeCut,sizeTail) := ConcurrentVertexBudgetRound.run (by decide) chain unit several 2 3 tape |
    throw (IO.userError "the size-mode chain trial did not return a cut")
  unless 0 < RationalVertexSparsityCode.count chain several sizeCut &&
      sizeTail == tape.drop (tape.length-sizeTail.length) do
    throw (IO.userError "the size-mode trial failed to separate an original demand")
  IO.println s!"PASS the generated vertex size plan separated an original demand at score {(large.receipt : ℚ)}"
  let some (freeCut,freeRest) := ConcurrentVertexBudgetRound.run (by decide) line free across 2 3 tape |
    throw (IO.userError "the affordable vertex branch returned no cut")
  unless freeCut.toList == [false,true,false] && freeRest == tape &&
      (RationalVertexSparsityCode.score line free across freeCut).value == 0 do
    throw (IO.userError "the free vertex branch changed the cut, original price or tape")
  IO.println "PASS a certified free internal vertex returned the original zero-price cut with the entire tape"
