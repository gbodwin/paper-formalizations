#!/usr/bin/env bash
set -euo pipefail

# Proposal only: load the unchanged Lake environment once.
# Each target still gets a fresh, sequential official checker process.
if [[ -n ${BASH_ENV-} || -n ${ENV-} ]]; then
  printf "%s\n" "Kernel replay requires absent shell startup hooks" >&2
  exit 2
fi
exec lake env "$BASH" --noprofile --norc -euo pipefail -c '
# Sequential replay avoids retaining all module environments simultaneously.
# Run from the repository root after lake build.
paper_source_dirs=(
  "A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners"
  "New Results on Linear Size Distance Preservers"
  "An Alternate Proof of Near-Optimal Light Spanners"
  "Unconditional Lower Bounds for Degree Fault Tolerant Spanners"
  "Light Edge Fault Tolerant Graph Spanners"
)
paper_libraries=(VFTSpanners LinearDistancePreservers LightSpanners DegreeFaultSpanners LightEFTSpanners)
for i in "${!paper_libraries[@]}"; do
  paper_source_dir="${paper_source_dirs[$i]}"
  for source in "$paper_source_dir/${paper_libraries[$i]}"/*.lean; do
    module="${source#"$paper_source_dir"/}"
    module="${module%.lean}"
    module="${module//\//.}"
    hash -r
    command leanchecker -v "$module"
  done
done
'
