#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
for module in CheckedEdgeOracle RandomizedEdgeFamily RandomizedEdgeFamilyParameters AdaptiveWidthEnvelope \
    PhysicalEdgeFamily PhysicalEdgeFamilyCost PhysicalBinaryEdgeFamily PhysicalBinaryEdgeFamilyCost \
    BinaryEdgeFamilyCalibration BinaryWeakDecomposition SelectedWeakCutLaw PhysicalWeakCutWire; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done
lake env timeout 360 lean "${flags[@]}" --run "$paper/verification/BestWeakCutSmoke.lean"
