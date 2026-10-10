# Fifth semantic component review

Result: **PASS within the exact component scope below.** No new semantic blocker found. This was a bounded read-only review of the frozen sources and relevant imported definitions/proofs, not a compiler run, repeat axiom audit, kernel replay, or final whole-paper audit.

Reviewed on 2026-10-10 (UTC):
- `local-check/LightEFTSpanners/HostGraphSampling.lean`
- `local-check/LightEFTSpanners/LargeCloudCertificate.lean`
- Relevant dependencies under `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/` and `repo/An Alternate Proof of Near-Optimal Light Spanners/LightSpanners/`.

## Frozen-source identity

Both SHA-256 digests were independently recomputed and match `fifth-source-hashes.json`:

- HostGraphSampling: `0a50479e89429b47d9c8039277d4c992daec9038cf4dcbb75cbd0c781394afcb`
- LargeCloudCertificate: `50e6a3f8f6f9a6ae9c84a7fe899c544018b9b8de85390ce46722bffe454c798e`

## HostGraphSampling: PASS

- `S` is an actual finite subset of candidate edges, obtained from the explicit powerset expectation and a finite maximum. Survival uses `B e ∩ U`, the cap and no-self condition, and probability `1/(2f)`, giving the valid `1/(4f)` bound including `f=1`.
- `X = T ⊔ edgeGraph S` is an actual graph below `G`. Candidates are input edges outside the seed; seed edges of `X` therefore belong to `T`.
- The explicit premise `∀ e ∈ U, Disjoint (B e) T.edgeFinset` is essential and correctly used. Together with sample survival and `S ⊆ U`, it proves that each retained candidate has no blocker anywhere in `X`, not merely no selected candidate blocker.
- Cleaning preserves the seed tree because `BlockingData.first_edge` prevents seed edges from having blockers. The imported construction supplies a Kruskal bottleneck spanning tree of the cleaned graph; the exchange theorem makes it minimum among actual spanning subgraphs. Deleting `T.edgeSet \\ K.edgeSet` retains `K`, preserves its minimum status, and gives `w(K) ≤ w(T)`.
- The weighted-girth argument uses actual cycles and an outside-tree maximum-weight edge. The retained candidate subset survives both cleaning and final deletion. Nonnegative edge weights justify passing its sum to `totalWeight R w`; the theorem exports the latter bound, while the subset argument is internal.
- The coarse bound uses exactly `(1+eps)*(2*k-1)+1`, not the paper's larger printed threshold. The imported substitution uses `δ = eps*(2*k-1)/(8*k)` and `δ ≥ eps/8`, yielding `8 + 2048/eps*n^(1/k)`.
- Strict positivity on input graph edges transfers to `R` and `K`. The explicit `n ≥ 2` premise makes `w(K)>0`, so clearing the lightness denominator is justified. With `f,k>0` and `eps>0`, the final bound is genuinely `sum(U) ≤ 4f*(8+2048/eps*n^(1/k))*w(T)`.

Exact scope: one supplied spanning host tree on the fixed finite vertex type, with supplied valid blocking data and blocker-disjoint candidates. This does not construct a global forest packing, assign candidates to hosts, transport graphs onto host subtypes, handle the singleton weight-bound case, or establish the optimized main upper theorem. No per-host lightness conclusion is assumed as a premise.

## LargeCloudCertificate: PASS

- `lift` has adjacency exactly when the base coordinates are adjacent. `afterFaults` deletes the supplied finite unordered-edge set; the preserver definition quantifies over every fault set of cardinality at most `q`, including sets containing nonedges.
- `exists_clean_cloud` proves an actual empty fault row by contradiction: selecting one fault in each row would inject all cloud indices into `F`. The unordered-edge orientation ambiguity is correctly excluded using the distinct base endpoints.
- Clean representatives at both ends yield the explicit three-edge cross-cloud walk. Composing two such reachability witnesses handles two vertices in one cloud.
- Base-walk induction is substantive: the nil case uses a neighbor, supplied by base connectedness and `Nontrivial V`; the cons case composes cross-cloud reachability with the induction hypothesis. `Nonempty I` supplies nonemptiness of the lifted graph.
- The final theorem has a connected spanning `T ≤ G` and strict `q < card(I)`. Every allowed fault set is therefore smaller than a cloud. The certificate lift stays connected after every such fault set; inclusion gives the reverse reachability implication.

Exact scope: a genuine all-fault connectivity certificate with enlarged clouds. This module proves no lower-weight theorem or optimal competitive-lightness lower bound. Choosing cloud size `q+1` changes the vertex scaling; at `q=cf`, the stated weight calculation has factor `(f+1)/(cf+1)^2` and base size `n/(cf+1)`. That calculation is not a theorem of this reviewed module. The independently invalid square-root-cloud denominator witness remains invalid; this certificate must not be represented as a repair of the original lower theorem.

## Remaining blockers outside this review

The global packing/subtype/assignment/optimized-upper-bound work and the original lower-theorem denominator/scaling gap remain outside these two passes. Passing compilation, allowed-axiom checks, and independent kernel replay does not discharge those semantic obligations.
