#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
modules=(BinarySourceSerialization BinarySourceFuel BinaryCoverReadback PhysicalSourceReadback
  PhysicalSolverChargeBounds PhysicalSolverCostEnvelope PhysicalAmplifiedBinaryVertex
  PhysicalAmplifiedBinaryEdge PhysicalBinaryEdgeCost PhysicalBinaryEdgeFamilyCost BinaryEdgeFamilyCalibration)
for module in "${modules[@]}"; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done
lake env timeout 900 lean "${flags[@]}" --run "$paper/verification/BinarySourceReadbackSmoke.lean"
lake env timeout 900 lean "${flags[@]}" --run "$paper/verification/AmplifiedPhysicalSolverSmoke.lean"
lake env timeout 900 lean "${flags[@]}" --run "$paper/verification/OriginalInputPhasesSmoke.lean"
lake env timeout 3600 lean "${flags[@]}" --run "$paper/verification/BinaryVertexPreparationSmoke.lean" --positive-source
lake env timeout 900 lean "${flags[@]}" --run "$paper/verification/BinaryEdgePreparationSmoke.lean"
lake env timeout 900 lean "${flags[@]}" --run "$paper/verification/BinaryAdaptiveFamilySmoke.lean"
lake env timeout 900 lean "${flags[@]}" --run "$paper/verification/BinaryIntegerCutoffSmoke.lean"
