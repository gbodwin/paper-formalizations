import DirectedFlowCutGap.BinaryWeakDecomposition

open DirectedFlowCutGap BinaryArithmetic BinaryRational

private def attempts : IO Unit := do
  let tree := BinaryFamilySampler.choose [40,70,40] 2
  let some ((first,paid),(rest,used)) := EncodedSolverBits.run tree [true,true,true,false,true] |
    throw (IO.userError "index rejection followed by acceptance did not finish")
  unless first == some 70 && rest == [true] && used == 4 && 0 < paid do
    throw (IO.userError "accepted sampled index, charge or suffix changed")
  IO.println s!"PASS rejected index 3 then selected index 1, read {used} bits, paid {paid}"
  let some ((failure,work),(tail,reads)) := EncodedSolverBits.run tree [true,true,true,true,false] |
    throw (IO.userError "bounded rejection did not finish")
  unless failure.isNone && tail == [false] && reads == 4 && 0 < work &&
      (EncodedSolverBits.run tree [true,true,true]).isNone do
    throw (IO.userError "bounded rejection or tape exhaustion picked a cut")
  IO.println s!"PASS two rejections report empty selection and a literal suffix, paid {work}"

private def selectFromOriginal : IO Unit := do
  let adj : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let half : Fraction := ⟨[true,false],[false,true,false],by decide⟩
  let w : RationalEdgeThresholds.Weights 2 := #v[#v[zero,half],#v[zero,zero]]
  let tape := [true,true,true,true,false,false,false,false,true,false]
  let some out := BinaryWeakDecomposition.run 2 1 0 adj w tape |
    throw (IO.userError "calibrated family and selection did not finish")
  unless out.cut == some ∅ && out.suffix == [true,false] && 0 < out.familyPaid && 0 < out.samplePaid do
    throw (IO.userError "selector changed the original weighted cut or suffix")
  IO.println s!"PASS actual original subunit family selected an empty cut after rejecting index 15, family {out.familyPaid}, selection {out.samplePaid}"
  let some failed := BinaryWeakDecomposition.run 2 1 0 adj w (List.replicate 8 true ++ [false]) |
    throw (IO.userError "family selection rejection did not preserve a result")
  unless failed.cut.isNone && failed.suffix == [false] && 0 < failed.samplePaid do
    throw (IO.userError "family selection rejection returned a cut or lost unread input")
  IO.println "PASS actual original family keeps bounded index rejection explicit"

def main : IO Unit := do
  attempts
  selectFromOriginal
