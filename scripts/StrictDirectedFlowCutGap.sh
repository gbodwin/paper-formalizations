#!/usr/bin/env bash
set -euo pipefail
# Run from the repository root after a successful clean lake build.
modules_text="$(python3 - <<'PY'
import json
from pathlib import Path
m = json.loads(Path("Improved Upper Bounds for the Directed Flow-Cut Gap/verification/component-verification.json").read_text())
assert m["strict_new_components_in_dependency_order"], "No strict compile targets"
print("\n".join(m["strict_new_components_in_dependency_order"]))
PY
)"
mapfile -t modules <<< "$modules_text"
for module in "${modules[@]}"; do
  lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/$module.lean"
done
