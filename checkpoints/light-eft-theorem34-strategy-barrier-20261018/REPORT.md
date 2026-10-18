# Conditional short-path strategy barrier: exact normalization and constants

Research base: **`c5f0837dba6578b5d6ef57e74c9c552b34a1bed3`**. Accepted Lean source remains **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. The parent reports independent acceptance of handwritten H–J, all 12 bindings, the residual-forest certificate, full-graph forcing and finite coverage. That review is not Lean execution. All previous candidate proofs, their stronger constants, raw artifacts and exact sampled/exhaustive labels remain unchanged.

This checkpoint consolidates the reviewer's proposed **conditional strategy barrier**. It is a handwritten proof awaiting independent review, not a new original-theorem error or a general impossibility theorem. **No new candidate experiment, compiler, Lean/kernel check, source edit, retrieval, extraction or site operation occurred.**

**Result:** under the precise hypotheses below, for each fixed f and q=2f,

`limsup_i R_(f,i) ≤ 2 L_f sqrt(q)/(q+1)`.                 (1)

Here R is the minimum genuine competitive lightness of an f-EFT 2-spanner, divided by the paper-target extremal function at the **full input order**. If `L_f=o(sqrt(f))`, the right side tends to zero as f grows. Thus this specified strategy cannot yield the positive f-independent coefficient required by Theorem 34's fixed-stretch-2 target. The original existential theorem and its completion scope are unchanged.

## 1. Exact conditional statement

For each integer f≥1 put q=2f. Let `L_f≥1` be a finite integer depending on f but **not** on the order-sequence index i. Consider any sequence of finite simple positive-weight graphs `G_(f,i)` with vertex sets V_(f,i), orders n_(f,i)→∞, and spanning edge-subgraphs K_(f,i) such that:

1. **All vertices counted.** Require `n_(f,i)≥2` for every f,i. K and G have the identical vertex set, including every helper, hub, auxiliary vertex and terminal. The n used below is this full order.
2. **Actual cuts.** Every nontrivial K cut has at least q+1 edges. Thus K is (q+1)-edge-connected. This is stronger than merely being a q-fault component preserver of some input.
3. **Specified weights.** For some `0<a_(f,i)≤1`, every K edge has weight a_(f,i); every edge of G outside K has weight exactly 1. The latter edges are called heavy. The weights are inherited by subgraphs. The value a may depend arbitrarily on f and i and need not converge or stay bounded away from zero.
4. **Uniform short-path packing.** For every heavy edge uv there are f+1 pairwise edge-disjoint u–v paths in K, each using at most L_f edges. Their packing can depend on uv and i, but the hop cap is the same L_f throughout the sequence. Edge-disjointness, not vertex-disjointness, is required.
5. **Fixed-parameter sparsity.** Writing `m_(f,i)=|E(K_(f,i))|`, require `m_(f,i)/n_(f,i)^2→0` as i→∞ for each fixed f. No rate uniform in f is assumed.

It is enough to consider increasing-order subsequences of any unbounded-order proposal, so n→∞ does not impose an all-n construction requirement. For a graph in this statement define

`D_q(G)=min{w(Q): Q⊆G is a q-fault component preserver of G}`,

where preservation is tested for **every** `F⊆E(G)` with |F|≤q and every vertex pair. Define S_f(G) to be the finite nonempty set of all f-EFT 2-spanners of G. Set

`M_(f,i)=floor(n_(f,i)/sqrt(q))`,
`R_(f,i)=min_(H∈S_f(G_(f,i))) [ w(H)/(D_q(G_(f,i)) lambda(M_(f,i),3)) ]`.       (2)

Thus the normalization is by the **actual minimum denominator**, then by the paper's exact extremal lambda at the full order divided by sqrt(2f). It is not division by a supplied certificate weight, by terminal order, or by a coarse lambda estimate. The floor is the explicit integer-order bookkeeping already used in the accepted research notes, not an amendment of the source theorem.

The proof establishes (1) for **every** such sequence, uniformly over all allowed choices of a_(f,i), path packings and geometry. It then proves the uniform-in-f exclusion when L_f=o(sqrt(f)). It does not assert that no individual fixed f can have a positive parameter-dependent lower coefficient.

## 2. Denominator and normalizer are well-defined

Suppress f,i temporarily and put n=|V|, m=|E(K)|, a=a_(f,i), L=L_f, s=q+1. Since K is a simple (q+1)-edge-connected spanning graph, every vertex has degree at least s and n≥q+2.

K remains connected after every q full-input faults: only F∩E(K) affects it. G is a supergraph, so K is an actual q-fault component preserver. The family defining D_q is finite and nonempty. Since the graph is connected, has at least two vertices and all edge weights are positive, D_q(G)>0.

Accepted Lemma A says each q-fault preserver Q must have at least `min(q+1,deg_G(v))=s` incident edges at every vertex. Every input edge has weight at least a. Summing its weighted degrees counts each retained edge twice, so

`D_q(G) ≥ a n s/2`.                                      (3)

This lower bound applies to **every** admissible denominator, not just K. In particular all helper vertices participate in it.

For any integer M≥2, the balanced unit complete bipartite graph has weighted girth >3 and lightness `floor(M²/4)/(M−1)≥M/4`. Therefore

`lambda(M,3) ≥ M/4 > 0`.                                 (4)

The extremal quantity is finite as well: in any positive connected simple M-vertex graph of weighted girth >3, a non-tree edge has weight less than its fundamental MST path, by the cycle inequality. Hence every edge weighs at most the total MST weight, and `lambda(M,3)≤M(M−1)/2`. Only the lower bound (4) is used quantitatively here.

Since n≥q+2 and q≥2, `floor(n/sqrt(q))≥2`. Thus every normalizer in (2) is finite and positive. G itself is always an f-EFT 2-spanner, so the minimum over S_f(G) exists. These positivity assertions are why the statement explicitly uses **0<a≤1**. Allowing a=0 would give K weight zero and D_q(G)=0, so the positive-denominator quotient used here could not simply be cancelled; that different convention is not covered.

## 3. Full-input fault argument in the cheap-spanner branch

Suppose `a L≤2`. We claim H=K is an f-EFT 2-spanner of the **full G**, not merely of a selected path graph.

Fix any `F⊆E(G)`, |F|≤f. For each surviving heavy edge uv, at most f of its f+1 edge-disjoint K paths can be hit, because an input-edge fault belongs to at most one of those paths. A heavy fault outside K hits none. A surviving packed path has weight at most aL≤2, twice the heavy edge weight. Every surviving K edge is retained directly with exactly its input weight a.

Expand each edge of any G−F path using these replacements; this gives a K−F walk of at most twice its weight. In particular, expanding an actual shortest G−F path proves the all-pairs stretch inequality. This remains valid when G has mixed heavy/cheap shortcuts: it does **not** assume the direct heavy edge has distance 1 in G−F. K−F and G−F are connected here because f≤q, so the compared distances are finite; the same edge-expansion proof respects the usual infinite-distance convention for unreachable pairs in general.

The packed paths are provided in K before F is chosen. No fault set is restricted to K, to a designated endpoint neighborhood, or to the edges of one proposed spanner. The surviving replacement for each edge may depend on F, as permitted by the EFT definition.

Using (3), w(K)=am and then (4),

`ell_q(K|G) ≤ 2m/(n s)`,
`R_(f,i) ≤ 8m/(n s M)` whenever aL≤2.                    (5)

The value a cancels without requiring a lower bound uniform over the sequence.

## 4. The other branch and the exact factor 2

Suppose `a L>2`. Then `1/a<L/2`. Use the always admissible output H=G. Simplicity and the fact that every edge has weight at most 1 give `w(G)≤n(n−1)/2`. With (3),

`ell_q(G|G) ≤ (n−1)/(a s) < L(n−1)/(2s)`.

Divide by the **actual** lambda and use (4):

`R_(f,i) < 2 L(n−1)/(s M)` whenever aL>2.                (6)

The factor 2 is precisely `4 × (1/2)`: the 4 comes from (4), and 1/2 from `1/a<L/2`. No density assumption is used in this branch. If L≤2 the branch is empty under a≤1; it need not be invented to cover that case. Equality aL=2 belongs to the admissible cheap-spanner branch, since stretch at most 2 allows equality.

Combining the branches gives the finite bound, regardless of which branch occurs at index i,

`R_(f,i) ≤ max{ 8m_(f,i)/[n_(f,i)(q+1)M_(f,i)],`
`                 2L_f(n_(f,i)−1)/[(q+1)M_(f,i)] }`.      (7)

The bound is independent of the weight choice. It does not require that a_i converge, that one branch eventually persists, or that an arbitrary certificate be a distance spanner.

## 5. Limits with the parameters in the correct order

Now fix f. Then q=2f and L_f are fixed finite numbers. As i→∞,

`M_(f,i)/n_(f,i) → 1/sqrt(q)`.

The first term in (7) is

`[8/(q+1)] [m_(f,i)/n_(f,i)^2] [n_(f,i)/M_(f,i)] → 0`,

by the stipulated fixed-f sparsity. The second tends to `2 L_f sqrt(q)/(q+1)`. Taking the limsup of the pointwise maximum proves (1). This also covers sequences alternating arbitrarily between the two weight branches. The inner limit has not exchanged order with f→∞, and the little-o rate is not assumed uniform in f.

If `L_f=o(sqrt(f))`, then

`2 L_f sqrt(2f)/(2f+1) ≤ sqrt(2) L_f/sqrt(f) → 0`.        (8)

For the paper target at c=2, a claimed uniform lower coefficient alpha(2)>0 would require `R_(f,i)≥alpha(2)` on an unbounded sequence of proposed witnesses for **every** f. Choose a sufficiently large fixed f_0 so that the right side of (1) is less than alpha(2)/2. The proved limsup bound then implies `R_(f_0,i)<alpha(2)` for all sufficiently large i. In each such graph at least one allowed output H defeats the claimed universal lower bound. No unbounded subsequence of that proposal rescues the coefficient.

The sufficiently-large-i threshold may depend on f_0 and on the proposed sequence; this is allowed. We first chose f_0, then grew order without bound at that fixed value. This is neither a forbidden uniform-onset assumption nor a high-f/small-n saturation diagonal. Since the proof applies to **any** sequence satisfying the hypotheses at that f, selecting a different such sequence or different weights does not escape the same bound.

This excludes the **specified strategy** with L_f=o(sqrt(f)), not all positive-weight input graphs. It does not refute Theorem 34, permit a coefficient depending on f in its place, or adopt a narrower stretch/completion scope.

## 6. Relation to the preserved candidate proofs

The earlier proofs are preserved verbatim at their immutable checkpoints. Literal special cases must satisfy all the assumptions above; a suggestive resemblance is insufficient.

| Prior candidate | Exact relation to this barrier |
|---|---|
| [Projective incidence, H–J](../light-eft-theorem34-incidence-20261018/REPORT.md) | Take K to be the full uniform-weight incidence graph, **not** its residual-forest cost certificate. It spans all 2m vertices, has min-cut p+1≥q+1, and each heavy pair has p+1≥f+1 disjoint paths of at most 4 hops. Thus L_f=4. For fixed f, primes p≥q grow and `|E(K)|/n²=(p+1)/(4m)→0`. The general bound is `8sqrt(q)/(q+1)`. The accepted candidate-specific bound `sqrt(q)/(q+1)` is sharper and remains unchanged; it uses the much smaller actual heavy-edge count. |
| [Shared hubs, all hubs short](../light-eft-theorem34-stretch2-20261018/REPORT.md) | This subfamily has uniform cheap K, includes every hub, has min-cut q+1, and provides f+1 distinct two-edge hub paths: L_f=2. For fixed f, `|E(K)|=2t(q+1)=O_f(n)=o(n²)`. Since its a≤1/4, it is always in the cheap branch, giving the stronger individual fixed-f limit R→0. |

The **mixed short/long shared-hub regimes are not literal instances** of this theorem: their spanning backbone has two weights, including 3/2, and deleting the long helpers to obtain a uniform cheap graph would violate the identical-vertex-set condition. Their accepted three-regime proof and uniform obstruction remain separate, valid results. No coefficient from that proof is weakened or silently replaced here.

Likewise the earlier two-cheap-block construction has a disconnected cheap subgraph; its genuine preserver adds unit-weight crossing edges. Its earlier fixed-stretch>1 cheap-spanner limitation remains proved separately. We do not misstate disconnected or mixed-weight examples as satisfying a globally edge-connected uniform-backbone theorem. The old obstructed near-extremal blowup family is not revisited.

## 7. Exact exclusions and future burden

The following are **outside this conditional statement**, not established successful escape constructions:

- A q-fault component preserver whose cheap subgraph is not globally (q+1)-edge-connected; relative preservation of small input cuts is a weaker notion.
- Nonuniform cheap weights, nonunit heavy weights or additional weight scales for which one common positive a does not control both path cost and the incident denominator bound.
- A backbone with nonvanishing quadratic edge density for fixed f, so the stipulated little-o argument is unavailable.
- Short-hop guarantees that grow with order instead of having one finite L_f per fixed parameter, or a necessary L_f that is not o(sqrt(f)).

To escape the **proved** barrier, a valid future witness strategy cannot satisfy all its hypotheses with L_f=o(sqrt(f)). Merely reducing pairwise common-neighbor overlap, or shrinking a, does not escape if the same short edge-disjoint path packing remains. Allowing L_f of order sqrt(f) or larger only makes this obstruction inconclusive; it does not prove forcing, a denominator bound, or a successful lower family. Density or different weights likewise require a new argument, not an asserted exemption from the original target.

For any proposed escape, retain the full graph when testing fault-forced heavy edges, verify actual component preservation for all input faults, count all helpers in n, and compare against the genuine D_q and exact lambda argument. Omitting helpers from n or from K is not a legitimate proof maneuver. A coefficient that vanishes with f is also not a repair of the intended uniform coefficient.

These exclusions do not prescribe individual-edge forcing as the only possible proof method; aggregate lower bounds remain logically available. Nothing here asserts that a future construction meeting the original target exists or that none can exist.

## 8. Proof-only evidence and disposition

No new candidate, graph instance or mathematical experiment was generated in this pass. In particular none of the previous experiment scripts or the synthetic runtime suite was rerun. Their raw outcomes and exhaustive-versus-targeted/sampled labels remain byte-identical. The only executed helper is a metadata/hash/preservation and idle-state seal; it does not test the mathematical theorem or invoke a compiler.

[Preservation](preservation.json), [commands](commands.txt) and [manifest](manifest.json) bind the proof text, the three prior research reports/manifests and the unchanged accepted evidence. The proposed barrier's derivation is now self-contained, but its mathematical acceptance is pending independent review. There is no new Lean formalization, source/status edit, retrieval/extraction, denied-cache retry, runtime/preparation change, site update or completion claim.

Publication is research-only with `[skip ci]` and exact remote verification. The worker then pauses idle for independent review, with the universal lock free and no compiler/checker process running.
