#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
modules=(InitialDemandFlagProgram InitialDemandPairProgram InitialDemandMaskProgram RepeatPointerProgram
  InitialUniformTables InitialRetainedStateProgram InitialGraphDictionary InitialGraphContexts InitialSeedProgram
  PhysicalControllerInitializer OriginalGraphControllerProgram OriginalGraphControllerLaw)

if [[ "${GITHUB_REF_NAME:-}" == codex/flow-raw-controller-20261119 ]]; then
  modules+=(BinaryGeometricCounterProgram OriginalControlWordsProgram PhysicalControllerControls
    RawGraphControllerProgram RawGraphControllerLaw RawGraphInputStore)
fi

for module in "${modules[@]}"; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done
lake env timeout 240 lean "${flags[@]}" --run "$paper/verification/InitialControllerSmoke.lean"
