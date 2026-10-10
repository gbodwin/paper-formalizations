#!/usr/bin/env bash
set -euo pipefail

# Sequential replay avoids retaining all module environments simultaneously.
# Run from the repository root after lake build.
paper_source_dirs=(
  "A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners"
  "New Results on Linear Size Distance Preservers"
  "An Alternate Proof of Near-Optimal Light Spanners"
  "Unconditional Lower Bounds for Degree Fault Tolerant Spanners"
  "Improved Upper Bounds for the Directed Flow-Cut Gap"
)
paper_libraries=(VFTSpanners LinearDistancePreservers LightSpanners DegreeFaultSpanners DirectedFlowCutGap)
for i in "${!paper_libraries[@]}"; do
  paper_source_dir="${paper_source_dirs[$i]}"
  for source in "$paper_source_dir/${paper_libraries[$i]}"/*.lean; do
    module="${source#"$paper_source_dir"/}"
    module="${module%.lean}"
    module="${module//\//.}"
    lake env leanchecker -v "$module"
  done
done

# The official leanchecker CLI treats a module argument as a prefix, so
# invoking it on DirectedFlowCutGap would launch every leaf again concurrently.
# Keep the same official replayFromImports path, but target the exact root.
echo "FLOWCUT_ROOT_RESOURCE_BEFORE"
free -m || true
for f in /sys/fs/cgroup/memory.current /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.events; do
  if [ -r "$f" ]; then echo "$f"; cat "$f"; fi
done
/usr/bin/time -v lake env lean -DautoImplicit=false -DwarningAsError=true scripts/ExactFlowCutRootReplay.lean
echo "FLOWCUT_ROOT_RESOURCE_AFTER"
free -m || true
for f in /sys/fs/cgroup/memory.current /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.events; do
  if [ -r "$f" ]; then echo "$f"; cat "$f"; fi
done
echo "FLOWCUT_ALL_LEAVES_AND_EXACT_ROOT_PASS"
