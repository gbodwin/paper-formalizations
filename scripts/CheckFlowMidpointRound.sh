#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
modules=(
  IntegerDistanceFromPhysical IntegerCellTestProgram IntegerLevelVertexProgram
  IntegerLevelCutProgram PhysicalSampledRoundProgram
)

for module in "${modules[@]}"; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done

for module in "${modules[@]}"; do
  lake env timeout 450 lean "${flags[@]}" --run "$paper/verification/${module}Smoke.lean"
done
