import LeanChecker
import Lean.Elab.Command

/-! Exact import-only root replay. The official CLI selects prefixes and
launches every matching module as an IO task. This invokes the same official
single-module kernel replay directly after all leaf replays have completed. -/
open Lean Elab Command
run_cmd do
  liftIO do
    initSearchPath (← findSysroot)
    IO.println "FLOWCUT_EXACT_ROOT_START DirectedFlowCutGap"
    (← IO.getStdout).flush
    replayFromImports `DirectedFlowCutGap
    IO.println "FLOWCUT_EXACT_ROOT_PASS DirectedFlowCutGap"
    (← IO.getStdout).flush
