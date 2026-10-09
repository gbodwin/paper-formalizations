# Verification of this partial checkpoint

This checkpoint contains 112 Lean source modules and the aggregate import file.
It remains a partial formalization of arXiv:2604.03412v3; full algorithmic and
polynomial bit-complexity claims are not yet certified.

- Lean 4.34.0; mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
- All included modules have warning-free compilation with autoImplicit=false;
  the current aggregate passed warningAsError=true.
- The fresh aggregate recursive audit checked all 6,920 distinct owned
  declarations, allowing only propext, Classical.choice and Quot.sound.
- Every module has an isolated official LeanChecker replay receipt. The
  unchanged 100-module baseline retains its exact-source checks; all twelve
  additions have fresh receipts. The current aggregate was replayed separately.
- Independent semantic and coverage reviews reconcile actual source/dependency
  hashes, all prior declaration owners and the 1,021 newly added declarations.
- Executed tests cover retained reverse cancellation, early stopping, concrete
  dictionary/index order, encoded candidate outputs, a substantive nonterminal
  sampled controller, changing-column rational covering updates, and literal
  bit decoding/rejection/default/adaptive-branch behavior.

The nonterminal run performed three family refreshes, two candidate solves,
one restart, one cut round and exactly one sampled epoch. Its final optimum was
zero and its returned cut was exactly the expected singleton. The rejection
frequency test for bound 3 and two two-bit trials gives one failure and five
occurrences of each accepted value among 16 equally likely raw inputs; this is
explicitly a bounded sampler with failure, not an exact uniform sampler.

The 100-module commit a2e89f1badd40b9b478aa50ad1b1bff587a3f08b passed the complete GitHub CI workflow in run 37909642183, completed 2026-10-09T09:35:42Z. This new commit's CI must be checked independently.

Source hashes are in verification/component-verification.json. Reproduce from
the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/RetainedPathSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/EarlyStopSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/CandidateFactorySmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/ConcreteCandidateSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/NonterminalControllerSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/FractionalCoverSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/FairBitSmoke.lean"
```

The small concrete candidate/controller tests can take several minutes in the
Lean interpreter. Whole-paper release still requires the actual graph fair-bit
adapter, complete input/operation/bit composition, weighted transformations,
constructive graph-cover oracle and objective guesses, and fresh final gates.
