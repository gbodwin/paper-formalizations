#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
modules=(
  EpochPermutationData EpochPrefixSelectionProgram EpochPermutationProgram ActiveDemandListProgram
  EpochGridTableProgram EpochMaterializeProgram PhysicalEpochInputData EpochActiveFromMaskProgram
  PhysicalEpochInputProgram
)

for module in "${modules[@]}"; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$module.lean"
  printf 'PASS strict elaboration of %s\n' "$module"
done
for fixture in EpochMaterializeSmoke PhysicalEpochInputSmoke; do
  lake env timeout 180 lean "${flags[@]}" --run "$paper/verification/$fixture.lean"
done
