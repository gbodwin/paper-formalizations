import DirectedFlowCutGap.EncodedSourceExecution

open DirectedFlowCutGap

private def edge : EncodedEdgeInput.Input 2 :=
  ⟨#v[#v[false, true], #v[false, false]], [(0, 1), (0, 1)],
    #v[BinaryRational.zero, ⟨[true, false], [true, false], by decide⟩,
      BinaryRational.zero, BinaryRational.zero]⟩

private def vertex : BinaryFractionalGuesses.Input 3 :=
  ⟨#v[#v[false, true, false], #v[false, false, true], #v[false, false, false]],
    [(0, 2)], #v[BinaryRational.one, BinaryRational.one, BinaryRational.one]⟩

private def tape : List Bool := [true, false, true]

def main : IO Unit := do
  let source := EncodedEdgeInput.encode edge
  match EncodedEdgeInput.parse source with
  | some ⟨n, decoded⟩ =>
    unless n == 2 && decoded.costs.toList.map (fun q => (q.num, q.den)) ==
        edge.costs.toList.map (fun q => (q.num, q.den)) do
      throw (IO.userError "the edge parser changed a padded cost field")
  | none => throw (IO.userError "the edge parser rejected its source")
  let shortCosts := (SourcePacking.capacityFields edge.costs).dropLast
  let invalid := PackingSourceInput.encode shortCosts (SourcePacking.matrixFields edge.adjacency)
    (SourcePacking.demandFields edge.demands)
  unless (EncodedEdgeInput.parse invalid).isNone do
    throw (IO.userError "the edge parser accepted a nonsquare cost table")
  match EncodedSourceExecution.edgeMass 0 source tape with
  | some ⟨n, .cut mask, rest, used⟩ =>
    unless n == 2 && (mask.toList.map Vector.toList) == [[false, true], [false, false]] &&
        rest == tape && used == 0 do
      throw (IO.userError "edge source execution changed the mask or the tape")
  | _ => throw (IO.userError "edge source execution did not return the cut")
  let vertexSource := SourcePacking.encode vertex.costs vertex.adjacency vertex.demands
  match EncodedSourceExecution.vertexSize 0 vertexSource tape with
  | some ⟨n, .cut mask, rest, used⟩ =>
    unless n == 3 && mask.toList == [false, true, false] && rest == tape && used == 0 do
      throw (IO.userError "vertex source execution changed the mask or the tape")
  | _ => throw (IO.userError "vertex source execution did not return the cut")
  let sample := EncodedAmplification.bitTree (fun x : Fin 3 => RawNonnegativeRational.Code.ofNat x.val)
    (FiniteDrawTrees.pick 3 (by decide)) 1 1 2
  match EncodedSolverBits.run sample [true, true, false, true, true, false, false] with
  | some (out, rest, used) =>
    unless out.val == 1 && rest == [false] && used == 6 do
      throw (IO.userError "the literal-bit interpreter lost a rejection or the unread suffix")
  | none => throw (IO.userError "the literal-bit interpreter exhausted a sufficient tape")
  IO.println "PASS source execution: exact edge fields, both graph paths, rejection, and random suffix"
