# Theorem 34: one bounded mathematical repair investigation

Research base: **`fd40832d552e4e9cedb5a5ad604180a73f1e65cb`**. Accepted mathematical source remains **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. This checkpoint contains handwritten mathematical arguments and small exact-rational experiments, **not Lean proofs or a general repair**. Independent mathematical review is pending. No accepted source, theorem status, correction log, proof/audit evidence, completed runtime module or website is changed. No compiler, Lean kernel checker, cache retrieval, extraction or cache advice ran.

**Outcome:** a genuinely different weighted construction proves the desired integer-rounded scaling at **stretch 1**, but has a provably cheap spanner at every fixed stretch above 1 for sufficiently large order. A weighted degree-cost lemma also shows that **no choice of connectivity certificate** repairs the advertised denominator cost on the previously reviewed near-extremal complete-base blowup family, uniformly in f. Neither result refutes Theorem 34. Its general stretch target remains open; this checkpoint does not propose replacing it with the stretch-1 special case.

## 1. Source, exact research target and scope

First read: the current [CORRECTIONS.md](../../Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/CORRECTIONS.md), followed by the original [arXiv v2 Theorem 34 and proof](https://arxiv.org/html/2502.10890v2#S4.SS2), Definitions 5, 7, 8 and 15, and the existing [fourth source audit](../../Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/verification/FOURTH_SOURCE_AND_COMPONENT_AUDIT.md). The original proof uses square-root-sized clouds, complete bipartite edge replacement, and an invalid MST-only denominator witness. That certificate defect and the sharp boundary p>q are **already reviewed facts**, not discoveries of this pass. Enlarging clouds to q+1 retains the already documented coefficient and vertex-order losses; it is not counted as a successful candidate here.

Use finite simple connected graphs with strictly positive edge weights. For integer q≥0 define

`D_q(G) = min{ w(Q) : Q⊆G preserves every connected component after every F⊆E(G), |F|≤q }`.

For graphs of order at least two, this finite minimum exists and is positive. Let `ell_q(H|G)=w(H)/D_q(G)`. An f-EFT k-spanner quantifies over **all** input-edge fault sets of size at most f and all vertex pairs, using the distances in the respective fault-deleted graphs. Unreachable distances are infinite; no finite/path-restricted distance is substituted. In the positive construction below Q remains connected under all q faults, so those compared distances are finite.

The intended uniform target investigated is: for every fixed real c≥2 there is a coefficient a(c)>0, independent of f and k, such that for every integer f≥1 and stretch k≥1 there are unbounded orders n admitting G with

`∀ f-EFT k-spanners H⊆G, ell_floor(cf)(H|G) ≥ a(c) lambda(floor(n/sqrt(cf)), k+1)`.

The definition of lambda takes an integer graph order. The paper writes its order argument without rounding; **floor is explicit bookkeeping for this research target**, not an approved source-theorem amendment. The full target includes at least every positive integer stretch, and no conclusion for just k=1 is treated as its replacement. Quantifier order permits the order threshold to depend on c,f,k: fix these parameters, then grow n without bound. No all-n uniform onset, f-versus-n restriction, or equality between differently rounded lambda arguments is assumed.

## 2. A cost test that every proposed certificate must satisfy

**Lemma A (truncated cuts and incident cost; proved here in ordinary mathematics).** For Q⊆G, q-fault component preservation is equivalent to

`|delta_Q(S)| ≥ min(q+1, |delta_G(S)|)` for every vertex set S.

Necessity: if Q has at most q crossing edges and omits a G crossing edge, delete precisely its crossing edges. Q has no crossing path, while a surviving G edge connects some opposite-side pair. This violates the component definition. Otherwise either Q has at least q+1 crossing edges or contains the entire G cut, which is the displayed condition.

Sufficiency: if Q−F disconnects a pair still joined in G−F, take S to be its Q−F component on one side. All Q crossing edges belong to F. Since |F|≤q, the displayed condition forces Q and G to have the identical crossing edge set; then G−F has no crossing edge either, a contradiction. This argument includes cuts of size zero and faults outside Q.

In particular each vertex v requires at least `r_v=min(q+1,deg_G(v))` incident Q edges. Let `L_r(v)` be the sum of the r cheapest incident G-edge weights, counted once per edge. Summing weighted degrees yields the necessary denominator bound

`D_q(G) ≥ (1/2) sum_v L_(r_v)(v)`.                    (A)

This tests actual vertex-level fault connectivity and weight simultaneously. It cannot be replaced by the number of edges in a whole cloud-to-cloud bundle.

## 3. Different candidate: two cheap dense blocks

**Lemma B (full k=1 lower bound for the explicit rounded target; proved here).** Fix any real c≥2 and integer f≥1. Put r=cf and q=floor(r), so q≥2f≥2. For each integer N≥q+2, let n=2N and partition V into two sets A,B of size N. Include every edge. Give each internal edge weight

`delta = 1/[N(N−1)] > 0`

and every crossing edge weight 1. Choose Q to contain all internal edges and any matching of q+1 crossing edges. These are actual simple input edges; N≥q+2 supplies enough distinct endpoints.

**Fault connectivity and denominator cost together.** Each internal K_N remains connected after q faults: every nontrivial clique cut has at least N−1≥q+1 edges. At least one of the q+1 selected crossing edges also survives. Thus Q−F is connected for every F⊆E(G), |F|≤q, including faults outside Q. Since Q⊆G, this proves the exact component-preserver property. Its internal weight is `N(N−1) delta=1`, so

`D_q(G) ≤ w(Q) = q+2`.                              (B1)

The A/B cut has N² G edges. Lemma A forces any q-fault preserver to retain at least q+1 crossing edges. Consequently the genuine optimum, without assuming Q optimal, satisfies

`q+1 ≤ D_q(G) ≤ q+2`.                              (B2)

**Spanner weight.** Every missing crossing edge uv has direct G distance 1, but any alternative uv path must have a crossing edge and at least one additional strictly positive edge, or multiple crossing edges. Its length is strictly greater than 1. Taking the permitted fault set F=∅ shows that every f-EFT 1-spanner contains all N² crossing edges. Hence

`ell_q(H|G) ≥ N²/(q+2) = n²/[4(q+2)]`.             (B3)

**Comparison with the actual extremal lambda.** For any positive connected m-vertex graph of weighted girth >2, each non-tree edge e has weight less than its MST path: the fundamental cycle has weight >2 times its maximum edge weight, which is at least w(e). Every edge therefore weighs at most the total MST weight. Since the graph is simple,

`lambda(m,2) ≤ m(m−1)/2 ≤ m²/2`.                   (B4)

Set M=floor(n/sqrt(r)); here M≥2. Then `lambda(M,2) ≤ n²/(2r)`. Since `2r ≥ q+2`, (B3) gives, for **every** eligible H,

`ell_q(H|G) ≥ (1/4) lambda(M,2)`.                  (B5)

The coefficient 1/4 is independent of c and f. For each fixed c,f the construction has unbounded order N→∞. It has the original square-root-f lambda argument at stretch 1 without using the failed cloud certificate. It does not alter the desired general theorem's quantifiers. Rescaling by N(N−1) would make all weights positive integers without changing any ratio or stretch assertion.

## 4. Why this candidate does not repair general stretch

**Lemma C (the same Q is cheap for k>1; proved here).** For the graph of Lemma B, Q itself is an f-EFT `(1+4 delta)`-spanner.

Indeed N≥q+2≥2f+2 implies N−2>f. For any two distinct vertices in the same block, the N−2 two-edge internal paths are edge-disjoint. After f faults, if the direct edge is missing one of those paths survives. If the edge survives, the shortest distance in both Q−F and G−F is delta. If it is missing, every path uses at least two edges, each of weight at least delta, and a two-edge internal path survives in Q; both shortest distances are 2 delta. Same-block distances are therefore preserved exactly.

For opposite blocks, at least one of Q's q+1 crossing edges survives. The two endpoints can reach its ports internally using at most 2 delta on each side, giving Q−F distance at most `1+4 delta`. G−F distance is at least 1. Coincident port endpoints only reduce this cost. Thus the claimed stretch holds for every actual input fault set of size ≤f, not merely for faults on Q.

Using (B2),

`ell_q(Q|G) ≤ (q+2)/(q+1) ≤ 4/3`.                  (C1)

For each fixed k>1, sufficiently large N has `1+4 delta ≤ k`. Thus the same candidate then has an eligible constant-ratio spanner. It cannot supply the growing target lower bound at general fixed stretch: cheap internal attachment that fixes the denominator also makes cheap detours. This is an obstruction **to this candidate**, not to the existence assertion of Theorem 34. No narrower theorem is proposed for adoption.

## 5. Stronger obstruction to merely replacing the old certificate

**Lemma D (an arbitrary-certificate weight obstruction for the reviewed family; proved here).**

Apply (A) to the **already reviewed near-extremal bases**, not to a newly alleged counterexample to the theorem. Let B_m be the complete graph on 0,...,m−1 with weights `w(i,j)=|i−j|+1`. The existing review established its weighted girth >2 and near-extremality. For completeness: a path of s≥2 edges has weight at least `|i−j|+s`, exceeding the direct edge; the consecutive path is an MST of weight 2(m−1); and

`w(B_m)=m(m−1)(m+4)/6`,
`ell(B_m)=m(m+4)/12 ≥ lambda(m,2)/6`.

The last inequality follows already from (B4), while `ell(B_m)≤lambda(m,2)` follows from admissibility. These bases meet the source's near-extremal premise; this fact is inherited, not presented as a new defect.

Choose any odd integer p≥3, set c=2, `f=(p²−1)/2`, and `q=2f=p²−1`. The source cloud size is **exactly** `ceil(sqrt(q+1))=p`. Let G be its full bipartite p-cloud blowup of B_m, with no internal cloud edges, and take any m≥p+1.

Every lifted vertex has degree p(m−1)≥p²=q+1. A q-fault preserver must therefore give each such vertex at least p² incident edges. Its incident weights are p repetitions of each base incident weight. If `a_(v,1)≤...` are the ordered incident base weights, then

`a_(v,i) ≥ i/2+1`,
`sum_(i=1)^p a_(v,i) ≥ p(p+5)/4`,

because at most two base neighbors occur at any integer distance. The p² cheapest incident lifted edges cost `p sum_(i=1)^p a_(v,i)`. There are p copies per base vertex. Lemma A gives, for **every certificate**, not only the MST-cloud choice,

`D_q(G) ≥ m p³(p+5)/8`.                            (D1)

In contrast, the paper's desired order of denominator cost is `p² w(MST(B_m))=2p²(m−1)`. Their ratio is at least

`D_q(G) / [p² w(MST(B_m))] ≥ m p(p+5)/[16(m−1)]`.

This grows quadratically with p, uniformly in m. No f-independent constant makes that desired certificate budget possible on these inputs.

The full input G itself is always an eligible f-EFT 1-spanner. In fact it is the only 1-spanner: any alternative lifted path with s≥2 edges projects to a base walk of weight at least `|i−j|+s`, greater than the direct edge weight. Its total weight is `p² w(B_m)`. From (D1),

`ell_q(G|G) ≤ 4(m−1)(m+4)/[3p(p+5)]`
`             = [16(m−1)/(m p(p+5))] ell(B_m)`
`             ≤ [16/(p(p+5))] ell(B_m)`.            (D2)

For the exact rounded target order `M=floor(mp/sqrt(p²−1))`, M≥m. Adding M−m pendant vertices with total positive weight tending to zero leaves weighted girth unchanged and makes lightness tend to ell(B_m); the definition as a supremum therefore implies `lambda(M,2)≥ell(B_m)`. Hence

`ell_q(G|G) ≤ [16/(p(p+5))] lambda(M,2)`.           (D3)

For any proposed positive f-independent coefficient, choose an odd p large enough to make this coefficient smaller, then hold its f fixed and let m grow without bound. Thus **this reviewed near-extremal blowup family cannot realize a uniform-in-f Theorem-34 reduction even with an arbitrary replacement certificate**. This is a weight-budget obstruction beyond the already known MST-certificate connectivity failure. It is not an all-n saturation diagonal: the bound holds for every m≥p+1 and consequently survives any parameter-dependent onset.

It is also **not a counterexample to Theorem 34**, which may choose different input graphs. Lemma B supplies such different graphs for k=1. The remaining problem is a genuinely different construction or transfer argument for general stretch, keeping the cheap-denominator and forced-spanner costs compatible. Simply supplying a different preserver on the same near-extremal blowups cannot suffice uniformly.

## 6. Finite experiments, proof status and stopping point

The executable [experiments.py](experiments.py) uses Python integer/Fraction arithmetic and explicit finite graphs. It invokes no compiler, proof kernel, solver, network or subprocess. [Raw log](experiments-01.log) and [results](experiment-results.json) retain all observations:

- N=4,q=2,f=1 and N=5,q=3,f=1: **15,633** actual input fault sets exhaustively checked for Q/G connectivity, including faults outside Q.
- **75** actual input fault sets checked for all-pairs rational distance comparison at stretch `1+4 delta`; no infinite distance was silently coerced.
- **41** missing heavy edges checked for strict distance increase at zero faults.
- **176** `(p,m)` instances checked the incident-weight formula, denominator lower bound and ratio algebra, for p∈{3,5,7,9}, p+1≤m≤50.

The finite checks passed on their first attempt; raw artifacts are preserved. They are evidence for the handwritten arguments, **not proofs of arbitrary-parameter statements and not Lean acceptance**. Lemmas A–D are proved in prose above and await independent mathematical review. No general-stretch replacement is proved or conjectured as established. The full target remains open; this coherent pass stops here rather than adopting a narrowed scope or reopening completed modules.

[Source bindings and preservation](preservation.json), [commands](commands.txt) and [manifest](manifest.json) bind this research checkpoint. Current disabled clean preparation, proof source, audits and all existing evidence remain intact. Authenticated cache retrieval remains denied and was not retried. No theorem/source status, site or completion claim is changed. Publication uses `[skip ci]`; after exact remote verification the worker is idle for independent review, with the universal lock free and no Lean/Lake/checker process.
