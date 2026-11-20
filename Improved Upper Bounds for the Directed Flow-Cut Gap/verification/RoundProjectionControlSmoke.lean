import DirectedFlowCutGap.PaidFramedEdgeCost

open DirectedFlowCutGap BinaryArithmetic
open PhysicalCoverAccess (Read)
open RawNonnegativeRational (Code)

private def sample : Bits → Read ((Bool × ℕ) × Bits)
  | [] => (none,5)
  | bit::rest => (some ((bit,2),rest),3)

private def withMoreWork (tape : Bits) : Read ((Bool × ℕ) × Bits) :=
  let r := sample tape
  (r.1,r.2+7)

def main : IO Unit := do
  let a : BinaryFractionalWalkOracle.Adjacency 2 := #v[#v[false,true],#v[false,false]]
  let c : Code := ⟨7,3,by decide⟩
  let costs : Vector (Vector Code 2) 2 := #v[#v[Code.zero,c],#v[Code.zero,Code.zero]]
  let D : EncodedEdgeLineInput.Input 2 := ⟨a,[(0,1)],costs⟩
  let line := EncodedEdgeLineInput.lineInput D
  let i := EncodedEdgeLineInput.edgeIndex (n:=2) (0,1)
  let weights := Vector.ofFn fun j => if i=j then Code.one else Code.zero
  let input : EncodedVertexSolver.RoundingInput (EncodedEdgeLineInput.lineSize 2) :=
    ⟨line.adjacency,weights,line.costs⟩
  let tape := [true,false,true]
  let round := PaidDirectEdgeWire.roundWithControl D .mass 2 input tape
  let some retained := round.1.1 | throw (IO.userError "the measured positive round failed")
  let some reference := PhysicalAmplifiedBinaryEdge.round D .mass 2 input tape
    | throw (IO.userError "the earlier positive round failed")
  unless retained.mask.toList == reference.mask.toList && retained.mask[i.val] &&
      retained.suffix == reference.suffix && retained.paid == reference.paid &&
      round.1.2 == reference.paid && 0 < round.2 do
    throw (IO.userError "the positive round changed its cut, suffix or earlier fee")
  IO.println s!"PASS positive original edge round kept arc and suffix {retained.suffix}, fee {retained.paid}, projection {round.2}"
  let graph : EncodedEdgeInput.Input 2 :=
    ⟨a,[(0,1)],#v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode graph
  let measured := PaidDirectEdgeWire.edgeWithRoundWork 0 .size source tape
  let some ⟨n,out⟩ := measured.1 | throw (IO.userError "the measured original edge source did not return")
  let .cut cut := out.output | throw (IO.userError "the measured original edge source produced a non-cut")
  let rejected := PaidDirectEdgeWire.edgeWithRoundWork 0 .size (source++[true]) tape
  unless n == 2 && cut.toList.map Vector.toList == [[false,true],[false,false]] && out.suffix == tape &&
      1784110573 < measured.2 && rejected.1.isNone && rejected.2 == 430370 do
    throw (IO.userError "original edge round accounting changed source behavior or lost work")
  IO.println s!"PASS original 44-bit edge kept cut and suffix {out.suffix}, paid with reached projections {measured.2}, trailing {rejected.2}"
  let short := PaidVertexAmplification.samples sample 3 [true]
  let shortMore := PaidVertexAmplification.samples withMoreWork 3 [true]
  unless short.1.isNone && shortMore.1.isNone && short.2 == 16 && shortMore.2 == 30 do
    throw (IO.userError "late tape exhaustion changed, or the skipped sample was charged")
  IO.println s!"PASS late sampling exhaustion kept two reached attempts, earlier fee {short.2}, with extra work {shortMore.2}"
