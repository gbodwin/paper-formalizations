#!/usr/bin/env bash
set -euo pipefail

# Replay each proof module in Lean's kernel. Sequential processes avoid
# retaining all imported environments at once on memory-limited machines.
# Run from the repository root, after lake build.
paper_source_dir="A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners"
for source in "$paper_source_dir"/VFTSpanners/*.lean; do
  module="${source#"$paper_source_dir"/}"
  module="${module%.lean}"
  module="${module//\//.}"
  lake env leanchecker -v "$module"
done
