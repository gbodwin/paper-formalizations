#!/bin/bash -p
# Source-only proposal. CI must start its step shell and this script with -p.
# The option must be in process argv at startup, not enabled after function import.
case $- in
  *p*)
    set -euo pipefail
    if [[ -n ${BASH_ENV-} || -n ${ENV-} ]]; then
      printf "%s\n" "Kernel replay requires absent shell startup hooks" >&2
      exit 2
    fi
    exec lake env /bin/bash --noprofile --norc -p -euo pipefail -c '
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
    ;;
  *)
    # Reserved arithmetic syntax cannot resolve to an imported exit/false function.
    (( 0 ))
    ;;
esac
