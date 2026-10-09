import LeanChecker
#eval do
  for m in #[`DirectedFlowCutGap.Basic, `DirectedFlowCutGap.MultiplicativeWeights, `DirectedFlowCutGap.PackingCovering, `DirectedFlowCutGap] do
    replayFromImports m
    IO.println s!"PASS kernel replay {m}"
