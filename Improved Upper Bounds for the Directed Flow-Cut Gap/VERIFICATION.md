# Verification of this partial checkpoint

This checkpoint contains 90 Lean source modules and the aggregate import file.
It is a partial formalization of arXiv:2604.03412v3. Full implementation and
polynomial operation/bit-complexity claims remain incomplete.

- Lean 4.34.0; mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
- Every included module has a warning-free compilation receipt with
  autoImplicit=false. The aggregate also compiled with warningAsError=true.
- A fresh aggregate audit recursively checked all 5,170 distinct owned
  declarations. Only propext, Classical.choice and Quot.sound were allowed.
- All 90 modules have isolated official LeanChecker replay receipts. The
  unchanged 80-module baseline retains its exact-source checks; all ten additions
  were checked freshly. The current aggregate was replayed separately.
- Independent semantic reviews checked the actual graph, optimization,
  probability, normalization and boundary-case contracts. An independent
  coverage review matched all included source and dependency hashes.
- Ordinary executable tests cover tabulated augmentation and closure, integer
  distances/cuts, permutation/cell tapes, retained arrays/cached control, and
  integer cost thresholds. The concrete full-controller test is terminal;
  nonterminal full execution and its joint output law are separate next gates.

The source hashes in verification/component-verification.json identify this
snapshot. Audit, replay and execution-test drivers are included. The 80-module
commit fb7b58c565522cb296eecb6d762325a085c51691 passed the complete GitHub CI
workflow in run 37900376325, completed 2026-10-09 at 08:07:15 UTC. CI for this
new commit must be checked at its own commit/run rather than inferred from that
prior result.

From the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/TabulatedRuntimeSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/IntegerDistancesSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/RetainedControlSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/FiniteSamplerSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/IntegerCostThresholdSmoke.lean"
```

Whole-paper release still requires completion of the remaining algorithmic
claims and a fresh final source/build/axiom/kernel/semantic review.
