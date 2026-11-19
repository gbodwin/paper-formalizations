#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
for module in BinaryAmplificationPreparation PhysicalVertexSampling PhysicalAmplifiedVertexSolver PhysicalAmplifiedVertexCost \
    CachedGuardedReferenceExecution PhysicalIntegerRounding PhysicalIntegerRoundingCost PhysicalSolverCostEnvelope WeakDecompositionOriginalFloor; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done
lake env timeout 900 lean "${flags[@]}" --run "$paper/verification/BinaryRoundBoundarySmoke.lean"
