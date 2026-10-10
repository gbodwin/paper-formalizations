# Statement map — arXiv:2510.10227v1

Full-paper verification is in progress. Theorem 1.3 is certified on exact CI in the finite simple graph/integer-s regime. Theorems 5.1 and 1.2 are also certified by exact-commit CI. The repaired union theorem and its simplified degree-weighted corollary have complete locally kernel-checked and independently reviewed proof chains; their new checkpoint CI is pending. The exact all-real 2/s exponent is false as stated; the new checked rounded/smooth real-s forest theorem is a valid repair. Real-s cut-theorem extensions remain unclaimed.

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
| Theorem 1.3 | Uniform parallel-greedy density/arboricity | Explicit density bound and a constructed partition into ceil(8s·n^(2/s)) actual forests; semantic review and exact CI pass; no Nash–Williams assumption |
| Lemma 4.2 / Appendix A | Repaired ordered-demand matching bridge | Actual 2|A|-copy matching union, exact volume edge count, and reversed-order parallel-greedy forest partition checked from SparseSequence; paired-orientation dispersion and final union bound now checked |
| Appendix A integral convention | Convert a feasible fractional witness to integral demand | Support-preserving factor-two extraction checked; actual fractional budgets and support geometry now proved and integrated |
| Theorem 4.1 / 1.4 | Union sparsity | Constructed integral union witness; explicit 512s·|A|^(2/s) ratio loss and 2048s·n^(4/s) sparse-sequence specialization; local gates and independent review pass, exact CI pending |
| Lemma 5.2 | Sparse cut cost at most φ times total node weight | Checked through full sparse-cut interface |
| Theorem 5.1 / 1.2 | Finite terminating sequence and decomposition bound | Direct unscaled construction checked with slack 8s·(2|A|)^(2/s), or 64s·n^(4/s) for unit capacities/degree weights; integer s ≥ 2; exact CI passed |

## Precise counting conventions

N enumerates actual oriented fixed-length strictly increasing walks. For 2r ≤ s+1, these are simple paths and N ≤ n². Weak counting requires nr ≤ 2m. Medium counting at m ≥ nr proves nr < 2N. Sampling uses exactly nr edges, an integer threshold for every r; the polynomial survival bound uses (m+1−r)^r rather than m^r. This only changes a uniform constant and yields the explicit density bound above, with r=(s+1)/2 handling odd s automatically. Empty graphs and low-density cases are included.

## Trust boundary

Lean 4.34.0, mathlib commit 5ed2965256430c3649e86755f9576b54eca72435. No original result is silently assumed; no `sorry`, new axiom, or unchecked native decision is accepted. `VERIFICATION.md` reports compilation, dependency audit, kernel replay, semantic-review scope, and exact-commit CI separately.

Nash–Williams and integral transportation are not silently imported. The integral extraction is proved from a bounded maximum and a charging argument. ForestCover and ForestPartition construct the actual edge partition, rather than stopping at density or a black-box arboricity criterion.

## Source corrections

See `CORRECTIONS.md`: directed-versus-undirected matching and integer-versus-fractional demand mismatches in Appendix A; the ratio-of-sums typo; sparsity supplies an inequality; and maximality certifies the unscaled sum rather than its larger rescaling. The main asymptotic theorems are not thereby refuted.

## Direct decomposition alternative

The final decomposition proof does not depend on the separate union theorem: the exact auxiliary edge count bounds the sum of witness volumes by the proved graph density. This, combined with per-cut sparsity and finite maximality, gives the cost and expansion of the unscaled sum directly. The earlier `exists_decomposition_of_union_cost_bound` remains conditional, but `exists_direct_decomposition` and `exists_degree_decomposition` do not use that premise.

## Repaired union construction

The input is any finite sequence of nonnegative cuts, with positive total attained witness volume. The proof constructs a sparse orientation of the actual 2|A|-copy matching graph, pairs incoming neighbors, projects the resulting integral list demand, and performs support-preserving integral extraction. It proves the original 2h-nearness and strict final h(s−1)-separation of every positive supported pair. The output cut is exactly `(1+1/(s−1)) * totalCut Cs`; its sparsity loss is at most **512s·|A|^(2/s)** times the ratio of total cut cost to total witness volume. The simplified theorem applies to nonempty sparse sequences, unit capacities, and original degree weights, with loss **2048s·n^(4/s)·φ**. Empty sequences are excluded from sparse-cut conclusions because they have no positive witness volume.

This replaces the problematic Appendix A construction; it does not certify its literal one-copy matching definition or fractional-as-integral demand. The arbitrary arboricity-oracle constant 8α(|A|,s) of Lemma 4.2 is not claimed. The actual proved parallel-greedy density is used constructively, which suffices for both main union theorems.

## Parameter-domain correction

The source theorem statements do not explicitly require integer s; Section 3 only implicitly does so through even/odd path counting. K_{a,a} at s=5/2 refutes the literal all-real exact 2/s exponent. `RealParameterArboricity` proves the valid all-real forest partition with rounded 2/floor(s), or smooth 4/s exponent. `RescalingCounterexample` proves actual graph-level failure of expansion monotonicity under length increases. Both modules pass local compilation, axiom audit, kernel replay and an independent semantic review.
