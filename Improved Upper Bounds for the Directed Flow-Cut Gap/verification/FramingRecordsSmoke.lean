import DirectedFlowCutGap.PhysicalSourceInputJoin

open DirectedFlowCutGap BinaryArithmetic

def main : IO Unit := do
  let input : EncodedEdgeInput.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],
      #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode input
  let suffix : Bits := [true,false,true]
  let measured := OriginalSourceFraming.readBinaryWithRecords (source++suffix)
  let reference := OriginalSourceFraming.readBinaryReference (source++suffix)
  let some framed := measured.1.1 | throw (IO.userError "complete source frames were lost")
  unless source.length == 44 && framed.source == suffix && measured.1.2 == reference.2 &&
      measured.1.2 == 216925 && 0 < measured.2 && measured.2 ≤ measured.1.2 do
    throw (IO.userError "the framer changed its completed state, fee or suffix")
  IO.println s!"PASS original 44-bit source frames preserved suffix {framed.source}, fee {measured.1.2}, record allocation {measured.2}"
  let mut most := 0
  for length in List.range source.length do
    let truncated := source.take length
    let rejected := OriginalSourceFraming.readBinaryWithRecords truncated
    let prior := OriginalSourceFraming.readBinaryReference truncated
    unless rejected.1.1.isNone && rejected.1.2 == prior.2 && 0 < rejected.2 && rejected.2 ≤ rejected.1.2 do
      throw (IO.userError s!"truncated prefix of length {length} changed its recorded rejection")
    most := max most rejected.2
  IO.println s!"PASS all 44 proper edge prefixes kept paid rejection, max record allocation {most}"
  let accepted := PhysicalSourceInputJoin.edgeWithFramingRecords source
  let rejected := PhysicalSourceInputJoin.edgeWithFramingRecords (source++[true])
  let empty := PhysicalSourceInputJoin.vertexWithFramingRecords (PackingSourceInput.encode [] [] [])
  let some ⟨n,typed⟩ := accepted.1.1 | throw (IO.userError "complete source failed typed reconstruction")
  unless n == 2 && typed.demands.map (fun d => (d.1.val,d.2.val)) == [(0,1)] &&
      accepted.1.2 == 430758 && 0 < accepted.2 && rejected.1.1.isNone && rejected.1.2 == 430370 &&
      rejected.2 == accepted.2 && empty.1.1.isSome && 0 < empty.2 do
    throw (IO.userError "edge or vertex typed source did not retain the reached framer allocations")
  IO.println s!"PASS typed edge accepted/trailing fees {accepted.1.2}/{rejected.1.2}, shared record allocation {accepted.2}, empty vertex allocation {empty.2}"
