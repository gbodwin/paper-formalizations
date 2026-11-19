#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
scratch=$(mktemp -d "${RUNNER_TEMP:-/tmp}/flow-library.XXXXXX")

lake env bash -c '
  cd "$1"
  lean -j1 --run ../.lake/packages/mathlib/scripts/mk_all.lean --check --lib DirectedFlowCutGap
' _ "$paper"

python3 - "$paper/verification/ConstructiveRoundingAudit.lean" "$scratch/LibraryAudit.lean" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text()
imports = source.index('import Lean.Compiler.Old')
scoped = 'if targets.contains mod then roots := roots.push name'
assert source.count(scoped) == 1
full = source[imports:].replace(scoped, 'roots := roots.push name')
Path(sys.argv[2]).write_text('import DirectedFlowCutGap\n' + full)
PY
lake env lean "${flags[@]}" "$scratch/LibraryAudit.lean"

for name in BinaryCutPriceSelection BinaryAllocationTrace; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$name.lean"
done
lake env lean "${flags[@]}" --run "$paper/verification/BinaryDeterministicStepsSmoke.lean"

lake env leanchecker -v DirectedFlowCutGap | tee "$scratch/kernel.log"
{
  sed -n 's/^import //p' "$paper/DirectedFlowCutGap.lean"
  printf '%s\n' DirectedFlowCutGap
} | LC_ALL=C sort > "$scratch/expected.txt"
sed -n 's/^replaying //p' "$scratch/kernel.log" | LC_ALL=C sort > "$scratch/replayed.txt"
cmp "$scratch/expected.txt" "$scratch/replayed.txt"
printf 'PASS exact library kernel replay of %s modules\n' "$(wc -l < "$scratch/replayed.txt")"
