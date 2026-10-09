#!/usr/bin/env bash
set -euo pipefail

# mk_all scans relative to its working directory rather than Lake's srcDir.
lake build mk_all
paper_source_dirs=(
  "A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners"
  "New Results on Linear Size Distance Preservers"
  "An Alternate Proof of Near-Optimal Light Spanners"
  "Unconditional Lower Bounds for Degree Fault Tolerant Spanners"
  "Improved Upper Bounds for the Directed Flow-Cut Gap"
)
paper_libraries=(VFTSpanners LinearDistancePreservers LightSpanners DegreeFaultSpanners DirectedFlowCutGap)
for i in "${!paper_libraries[@]}"; do
  lake env bash -c '
    cd "$1"
    exec ../.lake/packages/mathlib/.lake/build/bin/mk_all --check --lib "$2"
  ' _ "${paper_source_dirs[$i]}" "${paper_libraries[$i]}"
done
