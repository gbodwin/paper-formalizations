#!/usr/bin/env bash
set -euo pipefail
paper="Greedy Algorithms for Shortcut Sets and Hopsets"
for module in FiniteDistanceDP ChainTransitionCost ChainDistanceDP FiniteReachabilityDP ChainComputedFilter ChainExecutableObjective FiniteExecutableGreedy ChainExecutableGreedy ExecutableTraceBounds ChainExecutableMoment; do
  lake env lean -j1 -DwarningAsError=true -DautoImplicit=false "$paper/GreedyShortcuts/$module.lean"
done
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false "$paper/verification/ExecutableObjectiveFixtures.lean"
lake env lean -j1 -DwarningAsError=true -DautoImplicit=false "$paper/verification/ExecutableGreedyFixtures.lean"
