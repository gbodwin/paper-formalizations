# Statement map — arXiv:2510.10227v1

Full-paper verification is in progress. Theorem 1.3 has a complete constructed forest-partition proof; local kernel checks and independent semantic review pass, with exact-checkpoint CI pending. The union and final decomposition theorems remain open.

| Source | Obligation | Status |
|---|---|---|
| Definitions 2.2–2.4 | Integral ordered demands and node-weight constraints | Checked |
| Definitions 2.5–2.13 | Actual weighted graph cuts, volume, expander semantics | Component implementation checked |
| Definition 1.1 | Ordered matching model and earlier-walk exclusion | Checked; hereditary restriction proved |
| Lemma 3.2 | Unique highest edge forbidden on a short cycle | Checked |
| Lemma 3.3 | At most one fixed-length short increasing path per endpoint pair | Checked, including odd-s extension |
| Lemma 3.4 | Matching hikers; exact total 2|E|; exact-length weak counting | Checked, including conversion to actual simple paths |
| Lemma 3.5 | Deletion/medium counting | Checked through a constructed finite hitting set; 2m < nr + 2N |
| Lemma 3.6 | Fixed-size sampling/full counting | Checked by exact finite sample incidence counting and explicit walk transfer |
| Theorem 1.3 | Uniform parallel-greedy density/arboricity | Explicit density bound and a constructed partition into ceil(8s·n^(2/s)) actual forests; no Nash–Williams assumption |
| Lemma 4.2 / Appendix A | Repaired ordered-demand matching bridge | Actual 2|A|-copy matching union, exact volume edge count, and reversed-order parallel-greedy forest partition checked from SparseSequence; dispersion and final union bound pending |
| Appendix A integral convention | Convert a feasible fractional witness to integral demand | Support-preserving factor-two extraction checked; fractional input budgets still a bridge obligation |
| Theorem 4.1 / 1.4 | Union cost via the new arboricity bound | Pending |
| Lemma 5.2 | Sparse cut cost at most φ times total node weight | Checked through full sparse-cut interface |
| Theorem 5.1 / 1.2 | Finite terminating sequence and decomposition bound | Maximal sequence checked; reduction remains conditional on union-cost theorem |

## Precise counting conventions

N enumerates actual oriented fixed-length strictly increasing walks. For 2r ≤ s+1, these are simple paths and N ≤ n². Weak counting requires nr ≤ 2m. Medium counting at m ≥ nr proves nr < 2N. Sampling uses exactly nr edges, an integer threshold for every r; the polynomial survival bound uses (m+1−r)^r rather than m^r. This only changes a uniform constant and yields the explicit density bound above, with r=(s+1)/2 handling odd s automatically. Empty graphs and low-density cases are included.

## Trust boundary

Lean 4.34.0, mathlib commit 5ed2965256430c3649e86755f9576b54eca72435. No original result is silently assumed; no `sorry`, new axiom, or unchecked native decision is accepted. `VERIFICATION.md` reports compilation, dependency audit, kernel replay, semantic-review scope, and exact-commit CI separately.

Nash–Williams and integral transportation are not silently imported. The integral extraction is proved from a bounded maximum and a charging argument. ForestCover and ForestPartition construct the actual edge partition, rather than stopping at density or a black-box arboricity criterion.

## Source corrections

See `CORRECTIONS.md`: directed-versus-undirected matching and integer-versus-fractional demand mismatches in Appendix A; the ratio-of-sums typo; sparsity supplies an inequality; and maximality certifies the unscaled sum rather than its larger rescaling. The main asymptotic theorems are not thereby refuted.
