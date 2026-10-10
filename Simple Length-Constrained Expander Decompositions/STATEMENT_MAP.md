# Statement map — arXiv:2510.10227v1

Full-paper verification is in progress. No end-to-end main theorem is certified yet.

| Source | Obligation | Status |
|---|---|---|
| Definitions 2.2–2.4 | Integral ordered demands and node-weight constraints | Compiled initial module |
| Definitions 2.5–2.13 | Actual weighted graph cuts, volume, expander semantics | In progress |
| Definition 1.1 | Ordered matching model and earlier-walk exclusion | Implemented; compilation pending |
| Lemma 3.2 | Unique highest edge forbidden on a short cycle | Pending |
| Lemma 3.3 | At most one short monotone path per endpoint pair | In progress |
| Lemmas 3.4–3.6 | Hiker, deletion and fixed-size sampling counts | Pending |
| Theorem 1.3 | Explicit uniform parallel-greedy density/arboricity bound | Pending |
| Lemma 4.2 / Appendix A | Prior HHT24 union-of-cuts bridge, with precise trust boundary | Source audit in progress |
| Theorem 4.1 / 1.4 | Instantiate bridge with new arboricity bound | Pending |
| Lemma 5.2 | Sparse cut cost at most φ times total node weight | Witness-level inequality compiled; full cut interface in progress |
| Theorem 5.1 / 1.2 | Finite terminating sequence and decomposition bound | Pending |

## Imported background

Lean 4.34.0, mathlib commit 5ed2965256430c3649e86755f9576b54eca72435. Any use of Nash–Williams or a prior HHT24 result must be listed as an explicit mathematical input, with its exact statement and conventions. No original result may be silently assumed, and no `sorry`, new axiom or unchecked native decision is accepted as proof.

## Source audit concerns

The paper defines integral ordered demands with separate incoming/outgoing budgets, whereas Appendix A constructs undirected matchings on A(v) copies and later scales demands fractionally. These convention mismatches are undergoing independent review. The main asymptotic theorems are not thereby refuted. The displayed sum of ratios in the proof of Theorem 5.1 should be a ratio of sums; Definition 2.10 supplies ≤, not the equality printed in equation (5.1).
