#!/usr/bin/env bash
set -euo pipefail

# Check the two new lower-bound modules first with a diagnostic timeout.
# The complete sequential replay below remains mandatory.
for module in LinearDistancePreservers.UnweightedClique LinearDistancePreservers.TheoremFourDense; do
  timeout --kill-after=10s 180s lake env leanchecker -v "$module"
done

# Sequential replay avoids retaining all module environments simultaneously.
# Run from the repository root after lake build.
paper_source_dirs=(
  "A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners"
  "New Results on Linear Size Distance Preservers"
  "An Alternate Proof of Near-Optimal Light Spanners"
  "Unconditional Lower Bounds for Degree Fault Tolerant Spanners"
)
paper_libraries=(VFTSpanners LinearDistancePreservers LightSpanners DegreeFaultSpanners)
for i in "${!paper_libraries[@]}"; do
  paper_source_dir="${paper_source_dirs[$i]}"
  for source in "$paper_source_dir/${paper_libraries[$i]}"/*.lean; do
    module="${source#"$paper_source_dir"/}"
    module="${module%.lean}"
    module="${module//\//.}"
    lake env leanchecker -v "$module"
  done
done
