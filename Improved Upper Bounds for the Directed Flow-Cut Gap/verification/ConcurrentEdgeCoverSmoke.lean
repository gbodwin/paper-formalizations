import DirectedFlowCutGap.ConcurrentEdgeRound

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (Fraction zero)

private def one : Fraction := ⟨[true],[true],by decide⟩
private def A : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,false],#v[false,false,true],#v[false,false,false]]
private def C : RationalEdgeThresholds.Weights 3 :=
  #v[#v[zero,one,zero],#v[zero,zero,one],#v[zero,zero,zero]]
private def pairs : Vector (Fin 3 × Fin 3) 2 := #v[(0,1),(0,2)]
private def oneDemand : Vector (Fin 3 × Fin 3) 1 := #v[(0,2)]
private def freePrices : RationalEdgeThresholds.Weights 3 :=
  #v[#v[zero,one,one],#v[zero,zero,zero],#v[zero,zero,zero]]
private def shortcut : BinaryFractionalWalkOracle.Adjacency 3 :=
  #v[#v[false,true,true],#v[false,false,true],#v[false,false,false]]

def main : IO Unit := do
  let unit : FractionalCover.Row 9 := Vector.replicate 9 1
  let c := ConcurrentEdgeCover.priceRow A C
  let choice := ConcurrentEdgeOracle.oracle (by decide : 0 < 3) A pairs c unit
  let common := ConcurrentEdgeOracle.resource ((0,1) : Fin 3 × Fin 3)
  let endArc := ConcurrentEdgeOracle.resource ((1,2) : Fin 3 × Fin 3)
  unless MultiplicityCover.coeff choice.column common == 2 &&
      MultiplicityCover.coeff choice.column endArc == 1 && choice.pivot == common do
    throw (IO.userError "joint paths lost the multiplicity of the shared first arc")
  IO.println "PASS shortest-path profile counted the shared first arc twice and chose its price divided by two"
  let weights := ConcurrentEdgeCover.solve (by decide : 0 < 3) A C pairs
  let p := (BinaryRational.decode weights[0][1]).value
  let q := (BinaryRational.decode weights[1][2]).value
  let sum := 2*p+q
  let price := p+q
  unless sum ≥ 2 && price ≤ 3 do
    throw (IO.userError "the path-profile cover violated normalization or the comparison price")
  IO.println s!"PASS actual normalized length sum {(sum : ℚ)} and price {(price : ℚ)} against optimal price one"
  let tape := [true,false,true]
  let some (.cut mask tail) := ConcurrentEdgeRound.run (by decide : 0 < 3) A C pairs .size 0 tape |
    throw (IO.userError "the approximate lengths did not round to a cut")
  unless mask[0][1] && !(mask[0][0]) && !(mask[0][2]) && tail == tape do
    throw (IO.userError "the rounded profile failed to cut the shared original arc or preserve tape")
  IO.println s!"PASS path-profile lengths rounded the shared original arc with unread tape {tail}"
  let zeroWeights := ConcurrentEdgeCappedPrices.solve (by decide : 0 < 3) A freePrices oneDemand
  let directWeights := ConcurrentEdgeCappedPrices.solve (by decide : 0 < 3) shortcut freePrices oneDemand
  let length := fun (W : RationalEdgeThresholds.Weights 3) (s t : Fin 3) =>
    (BinaryRational.decode W[s.val][t.val]).value
  unless (ConcurrentEdgeZeroPrices.detect A freePrices oneDemand).isSome && length zeroWeights 0 1 == 0 &&
      length zeroWeights 1 2 == 1 do
    throw (IO.userError "removing free arcs failed to certify the zero-cost case")
  let some (.cut freeMask freeTail) := ConcurrentEdgeRound.run (by decide : 0 < 3)
      A freePrices oneDemand .mass 0 tape |
    throw (IO.userError "the free-arc branch did not return a cut")
  unless freeMask[1][2] && !(freeMask[0][1]) && freeTail == tape do
    throw (IO.userError "the free-arc branch used a positive price or changed the unread tape")
  IO.println "PASS free-arc test gave length one to the forced free arc and returned a zero-cost original cut with unchanged tape"
  let directPrice := length directWeights 0 1 + length directWeights 0 2
  let distance := RationalSparsestEdgeDistances.distance shortcut directWeights (0,2)
  unless (ConcurrentEdgeZeroPrices.detect shortcut freePrices oneDemand).isNone &&
      distance.isSome && 1 ≤ distance.getD 0 && directPrice ≤ 6 do
    throw (IO.userError "the positive-price path branch failed the rational perturbation bound")
  IO.println s!"PASS positive-path test used perturbed prices, shortest distance at least one and original price {(directPrice : ℚ)} against optimum one"
