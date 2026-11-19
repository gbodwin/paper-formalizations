import DirectedFlowCutGap.BinarySolverOuterControls

open DirectedFlowCutGap

private def checkControls (n κ : ℕ) : IO Unit := do
  let exponent := EncodedVertexAmplification.confidenceExponent n κ
  let v := BinarySolverOuterControls.vertex n κ
  let e := BinarySolverOuterControls.edge n κ
  unless v.draws == EncodedVertexAmplification.roundDrawBound n &&
      e.draws == EncodedEdgeSolver.drawBound n && v.extra == exponent && e.extra == exponent &&
      v.confidence == exponent+1 && e.confidence == exponent+1 && 0 < v.paid && 0 < e.paid do
    throw (IO.userError "binary solver controls differ from the retained draw or confidence law")
  IO.println s!"PASS dimension {n}, confidence degree width {κ.size}, vertex setup {v.paid}, edge setup {e.paid}"

def main : IO Unit := do
  checkControls 0 0
  checkControls 3 2
  checkControls (2^128+1) (2^80+7)
