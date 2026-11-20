import DirectedFlowCutGap.BinaryVertexReductionArithmetic

open DirectedFlowCutGap

private def fill (n : ℕ) : IO Unit := do
  let callback (i : Fin n) : ℕ × ℕ := (i.val^2+1,2*i.val+5)
  let observed := BinaryVertexReductionArithmetic.batch callback
  let measured := BinaryArrayBatch.run callback
  let ordered := (List.range n).map fun i => i^2+1
  let expectedFee := ((List.range n).map fun i => 2*i+5).sum+8*n+4
  unless observed.1.toList == ordered && observed.2 == expectedFee &&
      measured.1.1.toList == ordered && measured.1.2 == expectedFee &&
      0 < measured.2 && measured.2 ≤ BinaryArrayBatch.controlBudget n (2*n+5) do
    throw (IO.userError "the binary batch changed the output, order or callback fees")
  IO.println s!"PASS binary batch {n} entries in order, retained fee {observed.2}, scalar work {measured.2}"

def main : IO Unit := do
  fill 0
  fill 1
  fill 9
