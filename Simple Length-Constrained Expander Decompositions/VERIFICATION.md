# Verification record

## Repaired cut-sequence matching bridge checkpoint — 10 October 2026

All **25 paper modules** compiled with pinned Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b) and mathlib 5ed2965256430c3649e86755f9576b54eca72435.

- **412 declarations** passed the all-declarations audit, allowing only `propext`, `Classical.choice`, and `Quot.sound`. See `verification/axiom-audit.log` and the reproducible `Audit.lean`.
- All **25 modules** passed independent sequential Lean kernel replay. See `verification/kernel-check.log`.
- `verification/source-hashes.json` pins the checked sources. Root imports include every current paper module.
- Exact-commit CI for this new checkpoint is **pending publication**. The preceding forest-partition checkpoint [6da8e4bbfeb388755dc4aaced3617de0f8b5188f](https://github.com/gbodwin/paper-formalizations/commit/6da8e4bbfeb388755dc4aaced3617de0f8b5188f) passed build, module-index, and declaration-audit checks in [run 38059239134](https://github.com/gbodwin/paper-formalizations/actions/runs/38059239134); kernel replay is still running as of 14:30 UTC. The earlier 18-module checkpoint 9b9fbb747f6be2d11ce8a3db5f86d231b0966cfa passed all stages in [run 38057706991](https://github.com/gbodwin/paper-formalizations/actions/runs/38057706991). Older CI results do not certify newer sources.

### New proved scope

- The directed-demand repair now constructs the actual matching graph on separate outgoing/incoming copies: **2|A| vertices and exactly |D| edges**. Both copy allocations follow only from the original separate row/column budgets.
- Sequential near/far geometry proves different demands have disjoint support. The finite matching union has exactly the sum of demand sizes as its edge count, and reverse chronological labels satisfy the matching and earlier-walk exclusion conditions.
- The graph metric bridge replaces each copy edge by an actual short base-graph walk. No graph-homomorphism or unproved distance composition is assumed.
- `sparseSequence_matching_forest` chooses attained maximum witnesses directly from the original `SparseSequence`, proves all geometry using the actual prefix length-increase metrics, and constructs the auxiliary graph's forest partition. This completes the repaired Appendix A.2 bridge at the local proof level; its independent semantic review passes and exact CI remains pending.

- Short increasing graph walks are actual mathlib simple paths; long hiker trajectories are not incorrectly assumed simple.
- A finite hitting set, using at most one genuine edge per increasing walk, gives the exact deletion inequality 2m < nr + 2N and the medium counting lemma.
- Fixed-size sampling enumerates actual edge subsets, proves exact binomial incidence counting, and explicitly transfers surviving walks into the sampled graph. There is no assumed probabilistic independence or assumed path count.
- Combining that full count with dispersion proves an explicit uniform average-degree bound **d ≤ 8s·n^(2/s)** for s ≥ 2, including odd s, empty graphs, and low-density cases.
- The model is preserved by vertex restriction. Hereditary low-degree bounds construct an explicit finite elimination order with a uniform ceiling budget.
- The sparse elimination order constructs actual acyclic subgraphs by assigning each new vertex's later neighbors to distinct forests. Pruning to the earliest covering forest gives a genuine edge partition into **ceil(8s·n^(2/s)) forests**. This proves the explicit combinatorial conclusion of Theorem 1.3 for s ≥ 2; no arboricity oracle is assumed.
- A maximal supported integral demand is constructed from nonnegative fractional row/column budgets. Every positive supported pair has a saturated endpoint; charging proves fractional total ≤ 2 × integral total. Empty types and zero budgets are covered. This preserves support, not entrywise domination.

### Earlier checked scope retained

Finite integral demands and corrected algebraic bounds; actual weighted graph metrics and length-increase cuts; attained separated-demand volume; positive sparse witnesses; genuine ordered matching permutations and hikers with exact total traversal 2|E|; short-cycle and n² dispersion lemmas; finite maximal sparse-cut termination; and the conditional reduction returning the **unscaled** cut sum.

### Semantic review and unfinished work

The four hash-pinned semantic reviews in `verification/` independently cover the foundational graph/cut/termination modules, hiker/path/deletion/reduction modules, and all seven new sampling/density/hereditary/elimination/forest/extraction modules. The newest review reports no semantic failure and checks source alignment, exact finite sampling, integer rounding, odd s, empty graphs, unique edge partition membership, and the precise support-only extraction guarantee. The fourth review checks all five directed-copy matching and cut-sequence bridge modules and passes within the explicit h ≥ 0, integer s ≥ 2 regime. Compilation and kernel replay are separately recorded above.

Forest dispersion and its budgets and mass bound, the separated dispersed-witness bridge, union-cost theorem, and final decomposition results remain unfinished. Pairing and dispersion drafts are excluded from this checkpoint and from its checked scope. **Theorem 1.3 now has a complete Lean proof chain; exact-checkpoint CI is pending. The union and final decomposition theorems are not certified.** The decomposition reduction's `unionBound` remains a substantial explicit remaining obligation. Neither Nash–Williams nor integral transportation is silently assumed. The numerical scaled-maximality counterexample is independently checked mathematically, but its full graph-level Lean encoding is still pending.

### Private companion

The existing [private PaperLab](https://paperlab-length-expander-decompositions.greg-bodwin.chatgpt.site) was refreshed at source 04e848a3f1c3bed8724e215f65a46b10d8f93607, deployment appgdep_6aca4ac163d4819190f0787ddc8f7920. It contains the full reading edition, source corrections including unscaled maximality, and the preceding 298-declaration forest checkpoint. A refresh with the newest proofs remains pending.

JavaScript syntax, all 139 local anchors, and repeated/back/reset hiker-control behavior passed. Actual browser visual and accessibility QA remain unverified. See `verification/site-checks-20261010.log`.

Shared toolchain/dependency directories are reused read-only. Local compiler work uses one thread and the shared serialization lock. The other paper branches are unchanged.
