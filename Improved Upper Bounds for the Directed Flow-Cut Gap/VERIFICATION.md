# Verification of this partial checkpoint

This checkpoint contains 100 Lean source modules and the aggregate import file.
It is a partial formalization of arXiv:2604.03412v3. Full implementation and
polynomial operation/bit-complexity claims remain incomplete.

- Lean 4.34.0; mathlib commit 5ed2965256430c3649e86755f9576b54eca72435.
- Every included module has warning-free compilation with autoImplicit=false.
  The current aggregate also passed warningAsError=true.
- A fresh aggregate audit recursively checked all 5,899 distinct owned
  declarations, permitting only propext, Classical.choice and Quot.sound.
- All 100 modules have isolated official LeanChecker replay receipts. The
  unchanged 90-module baseline retains its exact-source checks; all ten additions
  were checked freshly. The current aggregate was replayed separately.
- Independent semantic and coverage reviews checked the graph, optimization,
  probability, representation and boundary-case contracts and exact source hashes.
- New executed tests cover reverse cancellation and repeated augmentation,
  capacity-table/numerator construction (including large integer encodings),
  computed reachable/infinite demand masks, concrete tape materialization and
  terminal single-pass execution. A substantive nonterminal controller execution
  test remains pending. The full state/output-law theorem itself is proved.

The source hashes in verification/component-verification.json identify this
snapshot. Audit, replay and execution-test drivers are included. The 90-module
commit 01804ff8e0b2d07dfbd76b89b62315f3d63a493a passed the complete GitHub CI
workflow in run 37904806362, completed 2026-10-09 at 08:42:12 UTC. This new
commit's CI result must be checked separately.

From the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/CountedFlowSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/EncodedCandidateSmoke.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/RetainedTapeSmoke.lean"
```

The counted path-coordinate relation is extensional and the encoded solver
assumes retained finite dictionaries. The stronger retained-edge/factory
backend, fair-bit sampling, complete input/arithmetic/bit costs, weighted
execution and constructive initial covering solver are not certified by this
checkpoint. Whole-paper release still requires those claims and a fresh final
source/build/axiom/kernel/semantic review.
