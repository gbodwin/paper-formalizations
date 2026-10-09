import LeanChecker
#eval do
  for m in #[`DirectedFlowCutGap.Basic, `DirectedFlowCutGap.CandidateOptimization, `DirectedFlowCutGap.EpochAccounting, `DirectedFlowCutGap.FiniteSurvival, `DirectedFlowCutGap.LevelCut, `DirectedFlowCutGap.LevelCutProbability, `DirectedFlowCutGap.MedianShortcuts, `DirectedFlowCutGap.MultiplicativeWeights, `DirectedFlowCutGap.PackingCovering, `DirectedFlowCutGap.PathExtraction, `DirectedFlowCutGap.PathSystemCounting, `DirectedFlowCutGap.ShortcutContraction, `DirectedFlowCutGap.TerminalPorts, `DirectedFlowCutGap.UnitCostReduction, `DirectedFlowCutGap.VertexFlow, `DirectedFlowCutGap.VertexReplication, `DirectedFlowCutGap.VertexRounding, `DirectedFlowCutGap.WitnessPrefix, `DirectedFlowCutGap.WitnessThinning, `DirectedFlowCutGap.ZeroWeights, `DirectedFlowCutGap] do
    replayFromImports m
    IO.println s!"PASS kernel replay {m}"
