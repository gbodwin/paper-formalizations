#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
modules=(
  NNRatStoredBounds RationalWeakFamily RationalWeakHorizon
  RationalEdgeThresholds RationalEdgeDecomposition AdaptiveOracleFailure
  CheckedEdgeOracle CheckedMWHistory RandomizedEdgeFamily RandomizedEdgeFamilyParameters
)
scratch=$(mktemp -d "${RUNNER_TEMP:-/tmp}/flow-adaptive.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

# Reuse the exact logical audit used by the constructive and package gates,
# with the adaptive modules as the audit roots.
python3 - "$paper/verification/ConstructiveRoundingAudit.lean" "$scratch/AdaptiveFamilyAudit.lean" "${modules[@]}" <<'PY'
from pathlib import Path
import sys

source = Path(sys.argv[1]).read_text()
source = 'import DirectedFlowCutGap.RandomizedEdgeFamilyParameters\n' + source[source.index('import Lean.Compiler.Old'):]
start = source.index('  let targets := #[')
stop = source.index('  let allowed', start)
targets = ',\n    '.join('`DirectedFlowCutGap.' + name for name in sys.argv[3:])
source = source[:start] + '  let targets := #[\n    ' + targets + ']\n' + source[stop:]
start = source.index('  for theoremName in #[')
stop = source.index('    let some (.thmInfo _)', start)
checks = """  for theoremName in #[
    `DirectedFlowCutGap.RationalEdgeThresholds.demands_iff,
    `DirectedFlowCutGap.RationalEdgeDecomposition.modified_feasible,
    `DirectedFlowCutGap.AdaptiveOracleFailure.within_reachable,
    `DirectedFlowCutGap.CheckedEdgeOracle.mass_failure,
    `DirectedFlowCutGap.RandomizedEdgeFamily.successful_family,
    `DirectedFlowCutGap.RandomizedEdgeFamily.tape_complete,
    `DirectedFlowCutGap.RandomizedEdgeFamily.calibrated_families] do
"""
source = source[:start] + checks + source[stop:]
Path(sys.argv[2]).write_text(source.replace('PASS constructive logical audit', 'PASS adaptive family logical audit'))
PY

for module in "${modules[@]}"; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done
lake env lean "${flags[@]}" "$scratch/AdaptiveFamilyAudit.lean"
for module in "${modules[@]}"; do
  lake env leanchecker -v "DirectedFlowCutGap.$module"
done
lake env timeout 450 lean "${flags[@]}" --run "$paper/verification/RandomizedEdgeFamilySmoke.lean"
