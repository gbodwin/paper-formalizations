#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
targets=(
  OptimalFlowCutBounds AdaptiveVertexBound AdaptiveEdgeBound
  WeakDecomposition WeakDecompositionBounds SparsestVertexCorollary SparsestEdgeCorollary
  IntegerClosureAsymptotic EncodedIntegerRounding EncodedUniformRounding EncodedWeightedRounding
)
for target in EncodedIntegerRounding EncodedUniformRounding EncodedWeightedRounding; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$target.lean"
done
lake env lean "${flags[@]}" "$paper/verification/ConstructiveRoundingAudit.lean"
for target in "${targets[@]}"; do
  lake env leanchecker -v "DirectedFlowCutGap.$target"
done
lake env lean "${flags[@]}" --run "$paper/verification/EncodedRoundingJoinSmoke.lean"
git diff --exit-code HEAD --
