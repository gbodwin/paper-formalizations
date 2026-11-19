#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
for name in EncodedEdgeGadget BinaryEdgeGadget PhysicalAmplifiedBinaryEdge PhysicalBinaryEdgeCost PhysicalPairedEdge; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$name.lean"
  printf 'PASS strict binary gadget layout module %s\n' "$name"
done
timeout 180 lake env lean "${flags[@]}" --run "$paper/verification/GadgetLayoutSmoke.lean"
timeout 900 lake env lean "${flags[@]}" --run "$paper/verification/BinaryEdgePreparationSmoke.lean"
