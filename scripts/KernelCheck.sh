#!/usr/bin/env bash
set -euo pipefail

# Sequential replay avoids retaining all module environments simultaneously.
# Run from the repository root after lake build.
paper_source_dirs=(
  "A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners"
  "New Results on Linear Size Distance Preservers"
  "An Alternate Proof of Near-Optimal Light Spanners"
  "Unconditional Lower Bounds for Degree Fault Tolerant Spanners"
  "Simple Length-Constrained Expander Decompositions"
)
paper_libraries=(VFTSpanners LinearDistancePreservers LightSpanners DegreeFaultSpanners LengthExpander)
for i in "${!paper_libraries[@]}"; do
  paper_source_dir="${paper_source_dirs[$i]}"
  for source in "$paper_source_dir/${paper_libraries[$i]}"/*.lean; do
    module="${source#"$paper_source_dir"/}"
    module="${module%.lean}"
    module="${module//\//.}"
    lake env leanchecker -v "$module"
  done
done
