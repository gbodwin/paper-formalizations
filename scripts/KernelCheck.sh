#!/usr/bin/env bash
set -euo pipefail

# Replay each proof module in Lean's kernel. Sequential processes avoid
# retaining all imported environments at once on memory-limited machines.
# Run from the repository root, after lake build.
for source in BodwinPapers/VFTSpanners/*.lean; do
  module="${source%.lean}"
  module="${module//\//.}"
  lake env leanchecker -v "$module"
done
