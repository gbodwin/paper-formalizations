# Verification of this partial checkpoint

This checkpoint contains 71 Lean source modules and the aggregate import file.
It is a partial formalization of arXiv:2604.03412v3. Full implementation and
polynomial operation/bit-complexity claims remain incomplete.

- Lean 4.34.0; mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
- Every included module has a warning-free compilation receipt with
  autoImplicit=false. The aggregate also compiled with warningAsError=true.
- A fresh aggregate audit recursively checked all 3,485 distinct owned
  declarations. Only propext, Classical.choice and Quot.sound were allowed.
- All 71 modules have isolated official LeanChecker replay receipts. The
  unchanged 52-module baseline retains its exact-source checks; all 19 additions
  were checked freshly. The current aggregate was replayed separately.
- Independent semantic reviews checked the actual graph, optimization,
  probability, normalization and boundary-case contracts. An independent
  coverage review matched all included source and dependency hashes.

The source hashes in verification/component-verification.json identify this
snapshot. The audit and replay drivers are included so the checks can be run
again. The previous 52-module commit 48a96c8aee84e84d44b552b9980eb082b62687ae
passed the complete GitHub CI workflow. CI for this new commit must be checked
at its own commit/run, rather than inferred from the prior result.

From the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
```

Whole-paper release still requires completion of the remaining algorithmic
claims and a fresh final source/build/axiom/kernel/semantic review.
