# Verification of this partial checkpoint

This checkpoint contains 130 Lean source modules and the aggregate import file.
It remains a partial formalization of arXiv:2604.03412v3. Full algorithmic and
polynomial bit-complexity claims are not yet certified.

- Lean 4.34.0; mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
- All included modules have warning-free compilation with autoImplicit=false;
  the aggregate also passed warningAsError=true.
- A fresh recursive audit checked all 8,073 distinct owned declarations,
  allowing only propext, Classical.choice and Quot.sound.
- Every source module has an isolated official LeanChecker replay. The exact
  unchanged 112-module baseline retains its checks; all eighteen additions
  have fresh source, object, dependency, execution and replay checks.
- The current aggregate was separately compiled, recursively audited, indexed
  by source ownership, and replayed. Independent semantic reviews reconcile
  the source and all final verification artifacts.

The new execution tests cover rational graph-cover updates, actual clone and
shortcut arrays, integer distance/midpoint/demand data, lazy rejection and
adaptive defaults, and a full nonterminal graph execution driven by literal
bits. That run consumes exactly two bit callbacks, performs one restart and
one cut round, and returns the expected singleton cut with zero final optimum.
The three-value bounded sampler intentionally has default-biased frequencies
6,5,5 on its sixteen equally likely two-trial inputs; the error is proved and
is not silently called uniform.

The preceding checked112 commit c7241492b8444075b22f86fb68ec781e730a2f4b passed
all GitHub CI stages in run37913297047 at 2026-10-09T10:14:19Z. This new commit's
CI must be checked independently. Source hashes are in
verification/component-verification.json.

Reproduce from the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/GraphCoverOracleSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/UnitCostInputSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/ShortcutInputSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/EncodedInputSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/LazyBitSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/NonterminalBitSmoke.lean"
```

The concrete nonterminal test can take several minutes in the Lean interpreter.
Whole-paper release still requires the remaining runtime, arithmetic, weighted
transformations, original-input LP and weak-decomposition compositions, followed
by complete final verification.
