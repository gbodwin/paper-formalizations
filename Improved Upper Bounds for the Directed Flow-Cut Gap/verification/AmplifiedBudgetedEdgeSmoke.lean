import DirectedFlowCutGap.AmplifiedBudgetedSparsestEdge

open DirectedFlowCutGap
open scoped NNRat
open BinaryRational (zero one)

private def forward : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
private def opposed : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[true,false]]
private def high : BinaryRational.Fraction :=
  (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat 4)).1
private def prices : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[high,zero]]
private def free : RationalEdgeThresholds.Weights 2 := #v[#v[zero,zero],#v[zero,zero]]
private def oneDemand : Vector (Fin 2 × Fin 2) 1 := #v[(0,1)]
private def twoDemands : Vector (Fin 2 × Fin 2) 2 := #v[(0,1),(1,0)]
private def forwardCut : RationalSparsestEdgeRound.Mask 2 := #v[#v[false,true],#v[false,false]]
private def backwardCut : RationalSparsestEdgeRound.Mask 2 := #v[#v[false,false],#v[true,false]]
private def bothArcs : RationalSparsestEdgeRound.Mask 2 := #v[#v[false,true],#v[true,false]]
private def tape := List.replicate 16384 false ++ [true,false,true]
private theorem nonemptyGraph : 0 < 2 := by decide

def main : IO Unit := do
  let score := RationalEdgeSparsityCode.score opposed prices twoDemands
  let cuts := #v[backwardCut,bothArcs,forwardCut]
  let selected := EncodedAmplification.minimum score 2 cuts.get
  unless (score forwardCut).value == 1 && (score backwardCut).value == 4 &&
      (score bothArcs).value == (5/2 : ℚ) && selected == forwardCut do
    throw (IO.userError "price per separated demand or the comparison was incorrect")
  IO.println "PASS original masks separated one, one and two demands with sparsity 1, 4 and 5/2, selecting 1"
  let some (cut, suffix) := AmplifiedBudgetedSparsestEdge.run nonemptyGraph
      forward prices oneDemand 2 3 tape |
    throw (IO.userError "the amplified solver ran out of bits on one arc")
  let used := tape.length - suffix.length
  unless cut == forwardCut && suffix == tape.drop used do
    throw (IO.userError "the repeated round changed the original cut or suffix")
  IO.println s!"PASS three trials picked the original one-arc cut and retained the tape suffix after {used} bits"
  let some (freeCut, freeSuffix) := AmplifiedBudgetedSparsestEdge.run nonemptyGraph
      forward free oneDemand 2 3 tape |
    throw (IO.userError "the amplified free path ran out of bits")
  let freeUsed := tape.length - freeSuffix.length
  unless freeCut == forwardCut && freeSuffix == tape.drop freeUsed &&
      (RationalEdgeSparsityCode.score forward free oneDemand freeCut).value == 0 do
    throw (IO.userError "the repeated free case returned a nonzero price or changed the original suffix")
  IO.println s!"PASS repeated free-arc branch picked a zero-cost cut and retained the suffix after {freeUsed} bits"
  let possible := #v[forwardCut,bothArcs,backwardCut]
  let samples := FiniteDrawTrees.map possible.get (FiniteDrawTrees.pick 3 (by decide))
  let program := EncodedAmplification.bitTree score samples 1 1 2
  let some (winner,tail,used) := EncodedSolverBits.run program [true,true,false,true,true,false,false] |
    throw (IO.userError "two scored samples did not complete on the supplied bits")
  unless winner == bothArcs && tail == [false] && used == 6 do
    throw (IO.userError "bounded rejection chose the wrong sampled arc mask or changed the suffix")
  IO.println "PASS bounded rejection read six literal bits and kept score 5/2 over 4, leaving [false]"
