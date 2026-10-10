# Fourth source and component audit

2026-10-10. Independent, bounded read-only review of the mathematical source and frozen Lean statements; no proofs changed, no compiler invoked, no external publication. This is not a whole-paper audit. Build, axiom-audit and kernel-replay statuses are the parent's existing checks, not rerun here.

## Decision

- **Notify the user about a verified proof-certificate defect in Theorem 34.** The proposed MST-cloud subgraph fails the source's actual fault-tolerant connectivity definition. The fixed-f infinite near-extremal family below removes the possible near-extremality/asymptotic loophole. This does **not** prove Theorem 34's lower bound false.
- **Do not announce the high-f diagonal as an unconditional asymptotic refutation.** Exact finite saturation is correct and contradicts a jointly uniform all-n interpretation of Theorems 11/12. The source's infinite-family formulation does not specify a uniform sufficiently-large-n threshold in f. Treat this separately as a statement-domain/quantifier clarification.
- The four newer component files match their frozen hashes and pass this bounded semantic review within their explicit hypotheses. Global host-tree construction and full upper-bound assembly are still outside their conclusions.

## 1. Actual source and permitted parameters

Source: arXiv:2502.10890v2, PDF SHA256 `8552afdf89b6a44ed642154379dfd3556bc6471cedb90c518733991123489b55`; extracted text SHA256 `acdb645018c6a6fe8f03d56427ddc8e91f532d15e90fff13294226413fb7ed68`. Both match `sources/SHA256.json`. I also rendered and visually inspected physical PDF pages 21–22, which are printed pages 20–21.

- Definition 1, printed p. 1, permits stretch k >= 1. Definition 5, p. 2, quantifies all vertex pairs and all input-edge fault sets F with |F| <= f.
- Definition 7, p. 3, requires the connected components of H\\F and G\\F to agree for every F subset of E of size at most f. It is neither a cloud-level statement nor restricted to faults that leave the proposed certificate connected.
- Definition 15, p. 9, defines lambda using a supremum of lightness over n-node graphs of weighted girth strictly greater than its threshold.
- Theorem 34, p. 20, starts with “For any constant c >= 2” and “an infinite family”; f and k are implicit parameters. Its proof chooses G' with weighted girth > k+1 and lightness Omega(lambda(n',k+1)), then p=ceil(sqrt(cf+1)) and n=n'p. Each original edge is replaced by its complete bipartite cloud graph. There are no intracloud edges.
- Printed p. 21 explicitly says that taking only the MST's complete-bipartite replacements is a valid cf-EFT connectivity preserver, and uses its weight to upper-bound the optimal denominator.
- No inspected global convention excludes c=2, f=1, k=1, positive unequal edge weights, or complete simple base graphs. Theorem 34 itself has no epsilon restriction. Theorems 11/12 explicitly allow every epsilon > 0; no global f-versus-n restriction was found.

## 2. Certificate obstruction and near-extremality

For the unit triangle, take its actual path MST, c=2, f=1, p=2. The full blowup is K_(2,2,2). The certificate contains the two complete bipartite links of the path. Delete the two certificate edges incident to one vertex u of a leaf cloud. The certificate isolates u, while G retains a direct edge from u to the other leaf cloud. These are two actual input edges, so Definition 7 fails directly.

The local six-vertex module proves actual MST status, weighted girth > 2, exact fault cardinality, input-edge membership, surviving source adjacency, and failure of reachability in the certificate. The generic module proves the same leaf obstruction for actual lifted graphs. For every complete base on at least three vertices, every spanning tree has a leaf with a non-tree neighbor. It also proves the exact rounding inequality ceil(sqrt(q+1)) <= q for every integer q >= 2. There is no choice-of-MST or rounding escape.

The packet's infinite near-extremal family is mathematically sound. For N >= 3, use the complete graph on 0,...,N-1 with w(i,j)=|i-j|+1. Every alternative path with r >= 2 edges has weight at least |i-j|+r > w(i,j). Removing a heaviest edge from any cycle therefore leaves a path heavier than that edge, proving weighted girth > 2. All edges have weight at least 2; the consecutive path has N-1 edges of weight 2 and is an MST. Direct summation gives

- w(G') = N(N-1)(N+4)/6;
- w(MST) = 2(N-1);
- lightness = N(N+4)/12.

For any positive connected simple N-node graph with weighted girth > 2, each non-tree edge weighs strictly less than its MST path, by its fundamental cycle. Hence every edge has weight at most w(MST), and lambda(N,2) <= N(N-1)/2. Consequently this complete family has lightness at least lambda(N,2)/6, uniformly in N. It meets the source's near-extremal initial premise. Keeping f=1 and p=2 while N grows preserves the certificate failure. This paragraph is independently checked mathematics, not a claim that the entire family argument has been formalized in Lean.

**Scope:** invalidating this proposed denominator witness invalidates that step of the written proof. It does not rule out a different cheap preserver or a different lower-bound construction.

## 3. High-f saturation: exact result, qualified source implication

The saturation module's finite theorem is correct for simple graphs, including disconnected ones: if q >= n-2, every q-EFT connectivity preserver Q of G equals G. Indeed, if uv is omitted, delete every Q-edge incident to u. There are at most n-2 of them because uv is missing. Q then isolates u while G retains uv. The module reaches this through the previously proved missing-edge degree bound. Its optimal denominator is the actual minimum over all preservers, with existence proved on the finite graph space. Taking H=G is an eligible spanner for nonnegative weights and stretch >= 1 and has ratio at most 1 (exactly 1 when total weight is positive).

Theorem 11 on printed p. 4 and Theorem 12 on p. 5 both literally begin “For all positive integers f, k, n” and display unindexed Omega lower bounds. Footnote 1 on p. 2 only explicitly defines O_x notation as hiding x-dependent factors. It does not separately formalize Omega or the uniformity of a sufficiently-large-n threshold. The p. 21 proof aims for an explicit 1/(4c) factor, independent of f; this supports an f-uniform coefficient in the intended reduction, conditional on the failed certificate step.

Under a jointly uniform reading with a positive coefficient and an n-threshold independent of f, the packet's diagonals work:

- Theorem 11: n=4m^2, f=2m^2, k=1, epsilon=1/2, giving q=2f=n.
- Theorem 12: n=4m^2, f=m^2, eta=2, k=1, epsilon=1/2, again q=n.

Both lambda arguments become lambda(2m,3). Unit K_(m,m) has weighted girth 4 and lightness m^2/(2m-1), which grows unboundedly, whereas saturation supplies an eligible ratio <= 1 in every input graph.

**Quantifier limit:** Theorem 34's “infinite family” is also compatible with fixing f before growing n. For fixed f, saturation concerns only finitely many n. An allowed threshold n0(f)>cf+2 excludes all these examples even if the Omega coefficient itself is independent of f. The paper does not explicitly settle this threshold dependence. Its literal all-n wording is stronger than that fixed-f reading, but the diagonal does not refute the latter. There is no basis here to silently assert that f-dependent thresholds are forbidden merely because Omega is unindexed. Raise this as a domain clarification if useful, not as a second settled asymptotic theorem disproof.

## 4. Newer four components

All four files in `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/` exactly match `review/third-source-hashes.json`.

- **StretchParameters:** The epsilon gap is exact. `corrected_threshold_lightness` uses actual weighted-girth semantics and an actual minimum spanning tree, with strictly positive graph-edge weights, epsilon>0 and natural k>0. The explicit 8+2048/epsilon*n^(1/k) bound is obtained by positive reparameterization into the imported actual-graph lightness theorem. It does not assume a lambda oracle or claim the larger printed threshold follows from the smaller threshold.
- **CounterfamilyGrowth:** The denominators are genuine simultaneous minimum two-/three-fault preservers of unit K_(m,m), whose existence and positive weights are proved in dependencies. The universal quantification is over actual 1-EFT stretch-5/2 spanners. The m=N^2 witness establishes failure of every proposed constant-times-sqrt(n) bound with n=2m, rather than merely a schematic inequality. It does not itself prove any statement about lambda.
- **GraphPruning:** `cleanGraph` really removes a first edge when a blocking partner survives in the sampled graph. `exists_finalPrune` requires a supplied host spanning tree T, T subset of X, all T-edges in the seed, and X intersect seed contained in T. It then constructs a bottleneck MST K of the cleaned graph and proves K remains an actual MST after final pruning, w(K)<=w(T), and actual weighted girth >t+1. The existence of this host T and the global forest packing/assignment are not proved here. No conclusion-shaped girth hypothesis is smuggled into these statements.
- **WeightedSampling:** `mass` is the explicit Bernoulli powerset mass and is normalized in the dependency. `surviving` is the exact rule e in S and no relevant blocker in S. Linearity and the heavy sample are derived by finite sums/maximization, with nonnegative weights, positive integer f, at most f blockers and no self-blocking. Sampling uses p=1/(2f), giving 1/(4f) survival including f=1. This is a theorem about random non-seed candidates. To connect it to a graph with deterministically retained host-tree edges, one must still establish that candidate blockers avoid that tree, as in the source's hosting condition (p. 12), and assemble the graph/weight wrappers. The component does not claim to discharge that missing global step.

## Reviewed local obstruction snapshots

- BlowupCertificateObstruction: `694e11c2cfc50c7ed1ca2db7c24e576fa46e14066d1847ce7c9a6fd3ecf5c24e`
- GenericBlowupFailure: `0fc0eaa4b8fc07b0c2937428e0eb89c14ba1b6315b3d9ac3e2b75421a2e4581f`
- FaultBudgetSaturation: `99fff90ae2b9625593781318687d839c6aa7ab22a60ad500ccf74a99f0c218b9`

The unrestricted finite fault-set quantifier in Lean is compatible with the source's F subset E: faults outside E have no effect and may be intersected away. More importantly, the explicit obstruction's fault edges are proved to lie in the input graph, so its source-level validity does not depend on that equivalence wrapper.

## Repair caveat

Increasing every cloud to p=q+1 for q=cf repairs this connectivity issue for a connected base with at least two vertices: the complete-bipartite blowup of a spanning tree remains connected after any q edge deletions (each tree-edge K_(p,p) has edge connectivity p). But the unchanged weight argument then yields only the coefficient (f+1)/(cf+1)^2 times base lightness, and the base has n/(cf+1) vertices. For constant c this is roughly an extra 1/f factor and linear-in-f vertex shrinkage instead of sqrt(f) shrinkage. It must not be advertised as restoring the original lower bound without a materially better construction or weight argument.
