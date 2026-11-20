import DirectedFlowCutGap.FramedSolverRecords

open DirectedFlowCutGap BinaryArithmetic

def main : IO Unit := do
  let graph : EncodedEdgeInput.Input 2 :=
    ⟨#v[#v[false,true],#v[false,false]],[(0,1)],
      #v[BinaryRational.zero,BinaryRational.one,BinaryRational.zero,BinaryRational.zero]⟩
  let source := EncodedEdgeInput.encode graph
  let tape : Bits := [true,false,true]
  let result := FramedSolverRecords.edge 0 .size source tape
  let some ⟨n,edge⟩ := result.1.1 | throw (IO.userError "the original edge solver did not return")
  let .cut arcs := edge.output | throw (IO.userError "the original edge solver did not return a cut")
  unless n == 2 && arcs.toList.map Vector.toList == [[false,true],[false,false]] &&
      edge.suffix == tape && result.1.2 == 1784110573 && result.2 == 3801 do
    throw (IO.userError "the recorded framer changed the paid original edge solver")
  let rejected := FramedSolverRecords.edge 0 .size (source++[true]) tape
  unless rejected.1.1.isNone && rejected.1.2 == 430370 && rejected.2 == 3801 do
    throw (IO.userError "trailing original source lost its framer work")
  IO.println s!"PASS paid 44-bit edge kept cut and suffix {edge.suffix}, fee {result.1.2}, records {result.2}, trailing {rejected.1.2}/{rejected.2}"
  let vertex := FramedSolverRecords.vertex 0 .size (PackingSourceInput.encode [] [] []) [true,false]
  let some ⟨m,answer⟩ := vertex.1.1 | throw (IO.userError "the original vertex solver did not return")
  let .cut empty := answer.output | throw (IO.userError "the original vertex solver did not return a cut")
  unless m == 0 && empty.toList.isEmpty && answer.suffix == [true,false] && vertex.1.2 == 3748215 && vertex.2 == 36 do
    throw (IO.userError "the recorded framer changed the paid original vertex solver")
  IO.println s!"PASS paid empty vertex kept cut and suffix {answer.suffix}, fee {vertex.1.2}, records {vertex.2}"
