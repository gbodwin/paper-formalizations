# Statement map — arXiv:2510.10227v1

Full-paper verification is in progress. No end-to-end main theorem is certified yet.

| Source | Obligation | Status |
|---|---|---|
| Definitions 2.2–2.4 | Integral ordered demands and node-weight constraints | Compiled, axiom-audited, kernel-replayed |
| Definitions 2.5–2.13 | Actual weighted graph cuts, volume, expander semantics | Component implementation checked; full bridge remains |
| Definition 1.1 | Ordered matching model and earlier-walk exclusion | Checked |
| Lemma 3.2 | Unique highest edge forbidden on a short cycle | Checked |
| Lemma 3.3 | At most one fixed-length short increasing walk per endpoint pair | Checked, including odd-s extension |
| Lemma 3.4 | Matching hiker process; total traversal 2|E|; exact-length weak counting | Checked as walks; path conversion and independent hiker review remain |
| Lemmas 3.5–3.6 | Deletion/medium counting and fixed-size sampling | Pending |
| Theorem 1.3 | Explicit uniform parallel-greedy density/arboricity bound | Pending |
| Lemma 4.2 / Appendix A | Repaired ordered-demand matching and integral extraction bridge | Source corrections confirmed; proof pending |
| Theorem 4.1 / 1.4 | Union cost via new arboricity bound | Pending |
| Lemma 5.2 | Sparse cut cost at most φ times total node weight | Checked through full sparse-cut interface |
| Theorem 5.1 / 1.2 | Finite terminating sequence and decomposition bound | Finite maximal sequence checked; reduction checked conditional on remaining union-cost theorem |

## Trust boundary

Lean 4.34.0, mathlib commit 5ed2965256430c3649e86755f9576b54eca72435. All 185 declarations passed an audit allowing only propext, Classical.choice, and Quot.sound; all 11 project modules passed independent kernel replay. Exact-commit CI is separately reported in `VERIFICATION.md`.

Any use of Nash–Williams, integral transportation, or a prior HHT24 result must be listed as an explicit mathematical input with its exact conventions. None is currently used to certify an end-to-end result. No original result may be silently assumed; no `sorry`, new axiom, or unchecked native decision is accepted as proof.

## Source corrections

See `CORRECTIONS.md`: directed-versus-undirected matching and integer-versus-fractional demand mismatches in Appendix A; the ratio-of-sums typo; sparsity supplies an inequality; and maximality certifies the unscaled sum rather than its larger rescaling. The main asymptotic theorems are not thereby refuted.
