#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
for module in BinarySolverOuterControls PhysicalAmplifiedBinaryVertex PhysicalAmplifiedBinaryEdge PhysicalBinaryEdgeCost SelectedWeakCutLaw; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done
lake env timeout 300 lean "${flags[@]}" --run "$paper/verification/BinarySolverOuterControlsSmoke.lean"
