import DirectedFlowCutGap.RationalDerivedEdgeFamily

open DirectedFlowCutGap
open scoped NNRat BigOperators

def main : IO Unit := do
  let zero := BinaryRational.zero
  let one := BinaryRational.one
  let half : BinaryRational.Fraction := ⟨(1 : ℕ).bits,(2 : ℕ).bits,by decide⟩
  let triangle : BinaryFractionalWalkOracle.Adjacency 3 :=
    #v[#v[false,true,false],#v[false,false,true],#v[true,false,false]]
  let triangleWeights : RationalEdgeThresholds.Weights 3 :=
    #v[#v[zero,half,zero],#v[zero,zero,half],#v[half,zero,zero]]
  let some violation := RationalInstanceEdgeFactor.counterprice triangle triangleWeights 1 |
    throw (IO.userError "a unit factor was accepted for the directed triangle")
  let price (e : Fin 3 × Fin 3) := violation (finProdFinEquiv e)
  let threshold := RationalEdgeThresholds.demands triangle triangleWeights
  let cuts := RationalExactEdgeOracle.candidates triangle threshold ∅
  let fractional : ℚ := ∑ e : Fin 3 × Fin 3, price e*(RationalEdgeDecomposition.originalWeight triangle triangleWeights e : ℚ)
  unless !cuts.isEmpty && cuts.all (fun cut => decide (1≤(∑ e ∈ cut, price e)-fractional)) &&
      (RationalInstanceEdgeFactor.counterprice triangle triangleWeights 2).isNone &&
      RationalInstanceEdgeFactor.least triangle triangleWeights == 2 do
    throw (IO.userError "the finite LP returned the wrong bound or violating price")
  IO.println s!"PASS directed triangle exact instance factor 2, accepted {cuts.length} cuts and rejected factor 1 with rational prices {[(price (0,1)), (price (1,2)), (price (2,0))]}"
  let A : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let w : RationalEdgeThresholds.Weights 2 := #v[#v[zero,one],#v[zero,zero]]
  let factor := RationalDerivedEdgeFamily.factor A w
  let L := (RationalDerivedEdgeFamily.family A w).cuts
  let suffix := [true,false,true]
  let tape := List.replicate (FairBitWords.width L.length) false ++ suffix
  let some ((some sample,_),(rest,used)) := RationalDerivedEdgeFamily.draw A w 1 tape |
    throw (IO.userError "the derived-factor family did not draw from its indexed cuts")
  unless factor == 1 && L.length == 21 && decide (sample = {(0,1)}) && rest == suffix && used == 5 do
    throw (IO.userError "the derived-factor draw changed the cut or literal suffix")
  IO.println s!"PASS single arc derived factor {(factor : ℚ)}, {L.length} cuts, drew after {used} bits and kept {rest} unread"
  let empty : BinaryFractionalWalkOracle.Adjacency 0 := #v[]
  let emptyWeights : RationalEdgeThresholds.Weights 0 := #v[]
  let some ((some sample,_),(rest,used)) := RationalDerivedEdgeFamily.draw empty emptyWeights 1 (false::suffix) |
    throw (IO.userError "the empty instance did not draw its empty cut")
  let some ((none,_),(rejected,read)) := RationalDerivedEdgeFamily.draw empty emptyWeights 1 (true::suffix) |
    throw (IO.userError "the out-of-range singleton draw did not reject")
  unless RationalDerivedEdgeFamily.factor empty emptyWeights == 0 && decide (sample = ∅) &&
      used == 1 && rest == suffix && read == 1 && rejected == suffix do
    throw (IO.userError "the empty derived-factor draw changed its cut or exact unread suffix")
  IO.println "PASS empty graph derived factor 0, accepted bit 0 and rejected bit 1, keeping the same unread suffix"
  let tiny : BinaryRational.Fraction := ⟨(2 : ℕ).bits,(25 : ℕ).bits,by decide⟩
  let sparse : BinaryFractionalWalkOracle.Adjacency 3 :=
    #v[#v[true,true,false],#v[true,true,false],#v[false,false,true]]
  let sparseWeights : RationalEdgeThresholds.Weights 3 :=
    #v[#v[tiny,one,zero],#v[tiny,tiny,zero],#v[zero,zero,tiny]]
  let k := RationalOriginalEdgeFamily.chooseScale sparse sparseWeights 1
  let sparseCuts := (RationalOriginalEdgeFamily.adaptive sparse sparseWeights 1).cuts
  let previousHorizon := RationalOriginalEdgeFamily.horizon sparse sparseWeights 1 9
  unless k == 5 && (RationalExactEdgeOracle.arcSet sparse).card == 5 &&
      0 < sparseCuts.length && sparseCuts.length < previousHorizon &&
      sparseCuts.all (fun X => decide (X = {(0,1)})) do
    throw (IO.userError "the sparse fallback did not use the original arc count and cuts")
  IO.println s!"PASS sparse fallback used {k} real arcs and produced {sparseCuts.length} cuts versus paired-vertex horizon {previousHorizon}"
