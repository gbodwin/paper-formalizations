#!/usr/bin/env bash
set -euo pipefail

# Run after building DirectedFlowCutGap.MedianShortcuts.
# Compare the new module against the pinned public recovery object.
base=a501d1c841b0dc28544c80f183f3ab940ebf792b
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
module='DirectedFlowCutGap/MedianShortcuts'
if ! git cat-file -e "$base^{commit}"; then
  git fetch --no-tags --depth=1 origin "$base"
fi
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/DirectedFlowCutGap"
git show "$base:$paper/$module.lean" > "$scratch/$module.lean"
export LEAN_NUM_THREADS=1
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true "$paper/$module.lean"
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true --root="$scratch" \
  -o "$scratch/$module.olean" "$scratch/$module.lean"
FLOW_MEDIAN_BASE_OBJECT="$scratch/$module.olean" lake env lean -j1 \
  -DautoImplicit=false -DwarningAsError=true "$paper/verification/MedianRepairAudit.lean"
lake env leanchecker -v DirectedFlowCutGap.MedianShortcuts
