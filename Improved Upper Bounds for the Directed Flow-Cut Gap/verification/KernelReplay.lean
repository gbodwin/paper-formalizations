import LeanChecker
#eval do
  for m in #[`DirectedFlowCutGap.Basic, `DirectedFlowCutGap.MultiplicativeWeights, `DirectedFlowCutGap.PackingCovering, `DirectedFlowCutGap.PathExtraction, `DirectedFlowCutGap.TerminalPorts, `DirectedFlowCutGap.VertexFlow, `DirectedFlowCutGap.WitnessThinning, `DirectedFlowCutGap.ZeroWeights, `DirectedFlowCutGap] do
    replayFromImports m
    IO.println s!"PASS kernel replay {m}"
