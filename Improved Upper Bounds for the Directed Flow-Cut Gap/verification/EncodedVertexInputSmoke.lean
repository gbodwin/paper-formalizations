import DirectedFlowCutGap.EncodedVertexAmplification

open DirectedFlowCutGap

private def input : BinaryFractionalGuesses.Input 3 :=
  ⟨#v[#v[false, true, false], #v[false, false, true], #v[false, false, false]],
   [(0, 2)],
   #v[BinaryRational.one, ⟨[true, true, true, false], [true, false], by decide⟩,
      BinaryRational.one]⟩

private def source : BinaryArithmetic.Bits :=
  SourcePacking.encode input.costs input.adjacency input.demands

private def zeroBit (n : ℕ) (h : 0 < n) : Id (Fin n) := pure ⟨0, h⟩

def main : IO Unit := do
  match EncodedVertexInput.parse source with
  | none => throw (IO.userError "valid graph input did not decode")
  | some ⟨n, D⟩ =>
    unless n == 3 &&
        D.costs.toList.map (fun q => (q.num, q.den)) ==
          input.costs.toList.map (fun q => (q.num, q.den)) &&
        D.demands.map (fun (s, t) => (s.val, t.val)) == [(0, 2)] do
      throw (IO.userError "parser changed dimensions, padded costs, or the original demands")
  match EncodedVertexAmplification.sourcePolynomialBitTree 1
      (fun _ => EncodedSizeRounding.tree) source with
  | none => throw (IO.userError "preserved bit input failed before the solver")
  | some ⟨_, tree⟩ =>
    match FiniteDrawTrees.execute zeroBit tree with
    | .cut mask =>
      unless mask.toList[1]? == some true do
        throw (IO.userError "parsed graph cut missed the unique internal vertex")
    | _ => throw (IO.userError "parsed graph returned no integral cut")
  let truncated := source.dropLast
  let trailing := source ++ [false]
  let zeroDen := PackingSourceInput.encode [([true], [])] [([false], [])] []
  let badShape := PackingSourceInput.encode [([true], [true])] [([], [])] []
  let badDemand := PackingSourceInput.encode [([true], [true])] [([false], [])] [([true], [])]
  unless [truncated, trailing, zeroDen, badShape, badDemand].all
      (fun bs => (EncodedVertexInput.parse bs).isNone) do
    throw (IO.userError "parser accepted a malformed source table")
  IO.println "PASS source-table vertex input: padded round trip, solved cut, and five rejections"
