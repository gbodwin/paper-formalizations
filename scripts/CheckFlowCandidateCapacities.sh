#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
modules=(
  ReferenceProgramSteps CandidateCapacityFlags CandidateCapacityWords
  CandidateLevelTestProgram CandidatePortAdjacencyProgram BinaryMinimumWordProgram
  CandidatePortGapProgram CandidateShiftSelectProgram CandidateTerminalFlagsProgram
  CandidateCapacityValues CandidateCoreCapacityProgram CandidateTerminalCapacityProgram
)

for module in "${modules[@]}"; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done

lake env timeout 450 lean "${flags[@]}" --run "$paper/verification/CandidateCapacitySmoke.lean"
