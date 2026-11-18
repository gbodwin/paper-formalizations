#!/usr/bin/env bash
set -euo pipefail

export LEAN_NUM_THREADS=1
paper='Improved Upper Bounds for the Directed Flow-Cut Gap'
flags=(-j1 -DautoImplicit=false -DwarningAsError=true)
new_sources=(
  EncodedIntegerRounding EncodedUniformRounding EncodedWeightedRounding
  EncodedSizeRounding EncodedCutSelection EncodedVertexSolver
  EncodedVertexInput EncodedAmplification EncodedVertexAmplification
  EncodedEdgeLabels EncodedEdgeGadget EncodedEdgeRounding
  EdgeLineReduction EncodedEdgeLineInput EncodedEdgeSolver WeakDecompositionExactWeight
  EncodedEdgeInput EncodedSolverBits EncodedSourceExecution
  FinalDispatchProgram FinalDispatchCallLift FinalDispatchCalls FinalDispatchPrefix
  FinalDispatchOutput FinalDispatchPositive FinalDispatchTail FinalDispatchTrace
  ActualFinalDispatch FinalDispatchEnvelope PackedOriginalStore OriginalStoreInputViews
  OriginalStoreInitial OriginalStoreCorrectness OriginalStoreDispatch
  PhysicalCoverReader PhysicalCoverExecution PhysicalSourceDispatch PhysicalVertexSolver PhysicalEdgeSolver
)
targets=(
  OptimalFlowCutBounds AdaptiveVertexBound AdaptiveEdgeBound
  WeakDecomposition WeakDecompositionBounds SparsestVertexCorollary SparsestEdgeCorollary
  IntegerClosureAsymptotic FractionalCoverRawGuesses
  "${new_sources[@]}"
)
for target in "${new_sources[@]}"; do
  lake env lean "${flags[@]}" "$paper/DirectedFlowCutGap/$target.lean"
done
lake env lean "${flags[@]}" "$paper/verification/ConstructiveRoundingAudit.lean"
for target in "${targets[@]}"; do
  lake env leanchecker -v "DirectedFlowCutGap.$target"
done
lake env lean "${flags[@]}" --run "$paper/verification/EncodedRoundingJoinSmoke.lean"
lake env lean "${flags[@]}" --run "$paper/verification/EncodedVertexSolverSmoke.lean"
lake env timeout 180 lean "${flags[@]}" --run "$paper/verification/EncodedAmplificationSmoke.lean"
lake env timeout 180 lean "${flags[@]}" --run "$paper/verification/EncodedEdgeRoundingSmoke.lean"
lake env timeout 180 lean "${flags[@]}" --run "$paper/verification/EncodedVertexInputSmoke.lean"
lake env timeout 180 lean "${flags[@]}" --run "$paper/verification/EncodedEdgeSolverSmoke.lean"
lake env timeout 180 lean "${flags[@]}" --run "$paper/verification/EncodedSourceExecutionSmoke.lean"
lake env timeout 180 lean "${flags[@]}" --run "$paper/verification/PhysicalVertexSolverSmoke.lean"
lake env timeout 180 lean "${flags[@]}" --run "$paper/verification/PhysicalEdgeSolverSmoke.lean"
git diff --exit-code HEAD --
