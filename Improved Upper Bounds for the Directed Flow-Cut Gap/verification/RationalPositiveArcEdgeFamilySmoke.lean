import DirectedFlowCutGap.RationalPositiveArcEdgeFamily

open DirectedFlowCutGap
open BinaryRational (zero one)
open scoped NNRat

private def A : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[true,true],#v[true,true]]
private def w : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[zero,zero]]
private def required : RationalExactEdgeOracle.Edge 2 := (0,1)

def main : IO Unit := do
  let k := RationalPositiveArcEdgeFamily.count A w
  let alpha := RationalDerivedEdgeFamily.factor A w
  let family := (RationalPositiveArcEdgeFamily.family A w).cuts
  unless (RationalExactEdgeOracle.arcSet A).card == 4 &&
      (RationalPositiveArcEdgeFamily.positiveArcs A w).card == 1 &&
      k == 1 && alpha == 1 && family.length == RationalOriginalEdgeFamily.horizon A w alpha k &&
      family.all (fun X => decide (X = {required})) do
    throw (IO.userError "the positive-arc family did not preserve the original graph and horizon")
  IO.println s!"PASS four actual arcs with one positive weight gave scale {k}, factor {(alpha : ℚ)}, and {family.length} valid original cuts"
  let tape := List.replicate (FairBitWords.width family.length) false ++ [true,false,true]
  let some ((some cut,_),rest,used) := RationalPositiveArcEdgeFamily.draw A w 1 tape |
    throw (IO.userError "the bounded draw did not return an original cut")
  unless cut == {required} && rest == tape.drop used && rest == [true,false,true] do
    throw (IO.userError "the positive-arc draw changed the cut or unread tape")
  IO.println s!"PASS the positive-arc family returned the original arc with {used} bits read and suffix {rest}"
