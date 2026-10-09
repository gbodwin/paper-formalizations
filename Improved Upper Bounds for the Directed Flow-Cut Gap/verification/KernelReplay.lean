import LeanChecker
#eval do
  for m in #[`DirectedFlowCutGap.Basic, `DirectedFlowCutGap.CandidateOptimization, `DirectedFlowCutGap.EpochAccounting, `DirectedFlowCutGap.FiniteSurvival, `DirectedFlowCutGap.LevelCut, `DirectedFlowCutGap.MultiplicativeWeights, `DirectedFlowCutGap.PackingCovering, `DirectedFlowCutGap.PathExtraction, `DirectedFlowCutGap.ShortcutContraction, `DirectedFlowCutGap.TerminalPorts, `DirectedFlowCutGap.VertexFlow, `DirectedFlowCutGap.VertexRounding, `DirectedFlowCutGap.WitnessThinning, `DirectedFlowCutGap.ZeroWeights, `DirectedFlowCutGap] do
    replayFromImports m
    IO.println s!"PASS kernel replay {m}"
