#!/usr/bin/env bash
set -euo pipefail

# mk_all scans relative to its working directory rather than Lake's srcDir.
# Run from the repository root, then check the index beside its source modules.
lake build mk_all
paper_source_dir="A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners"
lake env bash -c '
  cd "$1"
  exec ../.lake/packages/mathlib/.lake/build/bin/mk_all --check --lib VFTSpanners
' _ "$paper_source_dir"
