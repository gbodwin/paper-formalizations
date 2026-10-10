# Verification record

## Full counting, density, and integral-extraction checkpoint — 10 October 2026

All **18 paper modules** compiled with pinned Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b) and mathlib 5ed2965256430c3649e86755f9576b54eca72435.

- **281 declarations** passed the all-declarations audit, allowing only `propext`, `Classical.choice`, and `Quot.sound`. See `verification/axiom-audit.log` and the reproducible `Audit.lean`.
- All **18 modules** passed independent sequential Lean kernel replay. See `verification/kernel-check.log`.
- `verification/source-hashes.json` pins the checked sources. Root imports include every current paper module.
- Exact-commit remote CI for this new checkpoint is **pending publication**. The preceding checkpoint, [30646060efa95dacc63841bc24efe40a7c0d17d3](https://github.com/gbodwin/paper-formalizations/commit/30646060efa95dacc63841bc24efe40a7c0d17d3), passed every CI stage in [run 38056057761](https://github.com/gbodwin/paper-formalizations/actions/runs/38056057761). That older CI result does not certify the newer sources.

### New proved scope

- Short increasing graph walks are actual mathlib simple paths; long hiker trajectories are not incorrectly assumed simple.
- A finite hitting set, using at most one genuine edge per increasing walk, gives the exact deletion inequality 2m < nr + 2N and the medium counting lemma.
- Fixed-size sampling enumerates actual edge subsets, proves exact binomial incidence counting, and explicitly transfers surviving walks into the sampled graph. There is no assumed probabilistic independence or assumed path count.
- Combining that full count with dispersion proves an explicit uniform average-degree bound **d ≤ 8s·n^(2/s)** for s ≥ 2, including odd s, empty graphs, and low-density cases.
- The model is preserved by vertex restriction. Hereditary low-degree bounds construct an explicit finite elimination order with a uniform ceiling budget.
- A maximal supported integral demand is constructed from nonnegative fractional row/column budgets. Every positive supported pair has a saturated endpoint; charging proves fractional total ≤ 2 × integral total. Empty types and zero budgets are covered. This preserves support, not entrywise domination.

### Earlier checked scope retained

Finite integral demands and corrected algebraic bounds; actual weighted graph metrics and length-increase cuts; attained separated-demand volume; positive sparse witnesses; genuine ordered matching permutations and hikers with exact total traversal 2|E|; short-cycle and n² dispersion lemmas; finite maximal sparse-cut termination; and the conditional reduction returning the **unscaled** cut sum.

### Semantic review and unfinished work

The two hash-pinned semantic reviews in `verification/` independently cover the foundational graph/cut/termination modules and the hiker/path/deletion/reduction modules. The second also independently confirms the mathematical factor-two extraction strategy. It predates the final extraction implementation, sampling, density, hereditary, and elimination-order files; those newer files still need independent source-to-statement review. Compilation and kernel replay do not replace semantic review.

The forest-cover/arboricity construction, directed-copy demand-matching graph, forest dispersion and its budgets, geometric union bridge, union-cost theorem, and final decomposition results remain unfinished. **No end-to-end main theorem is certified.** The decomposition reduction's `unionBound` remains a substantial explicit remaining obligation. Neither Nash–Williams nor integral transportation is silently assumed. The numerical scaled-maximality counterexample is independently checked mathematically, but its full graph-level Lean encoding is still pending.

### Private companion

The existing [private PaperLab](https://paperlab-length-expander-decompositions.greg-bodwin.chatgpt.site) was refreshed at source f8cc4e3b1f26a3832a35bb2ff9c9ef26f49ffa5f, deployment appgdep_6aca3fabc624819193aeeab287747493. It contains the full reading edition, source corrections including unscaled maximality, and the preceding 185-declaration checkpoint. A refresh with the newest proofs remains pending.

JavaScript syntax, all 139 local anchors, and repeated/back/reset hiker-control behavior passed. Actual browser visual and accessibility QA remain unverified. See `verification/site-checks-20261010.log`.

Shared toolchain/dependency directories are reused read-only. Local compiler work uses one thread and the shared serialization lock. The other paper branches are unchanged.
