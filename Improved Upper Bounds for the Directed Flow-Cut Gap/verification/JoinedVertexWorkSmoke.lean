import DirectedFlowCutGap.PaidFramedVertexCost

open DirectedFlowCutGap BinaryArithmetic

private def obstruction : BinaryFractionalGuesses.Input 2 :=
  ⟨#v[#v[false,true],#v[false,false]],[(0,1)],#v[BinaryRational.one,BinaryRational.one]⟩

def main : IO Unit := do
  let tape : Bits := [true,false,true]
  let source := PackingSourceInput.encode [] [] []
  let empty := PaidFramedVertexWire.vertexWithJoinedWork 0 .size source tape
  let some ⟨n,cut⟩ := empty.1.1 | throw (IO.userError "empty original vertex source did not return")
  let .cut mask := cut.output | throw (IO.userError "empty original vertex source did not return a cut")
  unless n == 0 && mask.toList.isEmpty && cut.suffix == tape && empty.1.2 == 3748215 &&
      empty.2.1 == 1502578 && empty.2.2 == 36 do
    throw (IO.userError "the combined vertex execution changed its original result or reached counts")
  IO.println s!"PASS empty joined vertex kept cut and suffix {cut.suffix}, fee {empty.1.2}, cache {empty.2.1}, frames {empty.2.2}"
  let invalid := PaidFramedVertexWire.vertexWithJoinedWork 0 .mass (source++[true]) tape
  unless invalid.1.1.isNone && invalid.2.1 == 0 && invalid.2.2 == 36 do
    throw (IO.userError "vertex source rejection lost the framer or reached an unvisited phase")
  IO.println s!"PASS joined vertex trailing rejection kept fee {invalid.1.2}, cache {invalid.2.1}, frames {invalid.2.2}"
  let input := SourcePacking.encode obstruction.costs obstruction.adjacency obstruction.demands
  let reply := PaidFramedVertexWire.vertexWithJoinedWork 0 .mass input tape
  let some ⟨m,out⟩ := reply.1.1 | throw (IO.userError "joined vertex obstruction did not return")
  let .infeasible (s,t) := out.output | throw (IO.userError "the original vertex obstruction was lost")
  unless input.length == 36 && m == 2 && (s.val,t.val) == (0,1) && out.suffix == tape &&
      reply.2.1 == 7668311 && 0 < reply.2.2 do
    throw (IO.userError "the joined vertex obstruction or its observed counts changed")
  IO.println s!"PASS 36-bit joined vertex kept obstruction ({s.val}, {t.val}) and suffix {out.suffix}, fee {reply.1.2}, cache {reply.2.1}, frames {reply.2.2}"
