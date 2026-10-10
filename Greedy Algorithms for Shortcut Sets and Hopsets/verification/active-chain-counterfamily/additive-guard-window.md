# Logarithmic chain-path repair: an additive-depletion theorem and the remaining gap

Date: 2026-10-10. Ordinary mathematical proof of an additive guard-depletion theorem for the actual chain potential. The universal logarithmic repair remains unresolved.

## Result

The proposed universal logarithmic path assertion is **not proved or refuted here**. The existing stretched-tree counterexample refutes its constant-factor predecessor, but does not refute the logarithmic assertion.

There is, however, an unconditional weaker geometric statement. It supplies an actual minimum path and a rectangle of genuine old rebased distances, without assuming rebased optimality or introducing a progress oracle.

**Additive-depletion window theorem.** Fix any legal state H and any important pair (s,t₀), and put L=d_H(s,t₀). Let

    E_s(t) = { e(s,C) : s reaches C in original G, and e(s,C) reaches t in original G },
    K = |E_s(t₀)|.

Here e(s,C) is the original-source earliest vertex, not a selector recomputed in an augmented graph. Different nonempty chains give different entry vertices. In particular L≤K≤the number of nonempty chains≤n.

If L²≥64K, set the positive integer

    k = floor(L²/(64K)).

Then there are an important pair (s,t*) and an actual minimum s-valid path P to t*, visiting M≥L/2 distinct chains, with the following property. Write a_i for the LAST vertex of P's i-th chain and b_j for the FIRST vertex of its j-th chain. For every

    1≤i≤k,          M−k+1≤j≤M,

we have the actual rebased lower bound

    d_H(a_i,b_j) ≥ 4k.

Consequently the single legal edge

    a_k → b_(M−k+1)

has raw-potential decrease at least 2k³. Whenever the actual algorithm has not reached its separate stopping condition, its selected potential-greedy edge has at least this decrease.

The statement holds for arbitrary legal H, and requires no assumption that H was reached by greedy insertions. It also holds when L is the global maximum, as in the question. Taking K to be the number of all chains reachable from s is a valid weaker version; the interval-entry definition above gives the tighter statement.

This is a scale L²/K result. It does **not** establish the proposed L/log n scale in general, or establish the paper's claimed cubic progress or final near-linear greedy-stage bound.

## Source alignment

The source is arXiv:2511.20111v2, especially the definition of source-dependent validity and the unsupported hereditary-minimum claim in the proof of Lemma 5.7. The formal ingredients inspected were ChainDistance, ChainImportantPairs, ChainGuard, ChainSubwalk, ChainInteriorSavings, ChainRectangleCharging, ChainGuardSeparation, and the supporting ChainCounting/ChainEntries modules.

Distances below are always actual minima in the fixed source's filtered augmented graph. H and internal preprocessing contain only original-closure edges. All reachability statements and entry selectors use original G. Chain contiguity and distinct entries follow from the existing DAG/entry-filter facts. Uncovered vertices have zero chain cost and cause no change to the counting below.

No claim of Lean compilation is made for this new theorem: this file is its mathematical proof.

## 1. Prefix optimality with the source unchanged

Let P be an actual minimum s-valid path to an important t, with chain sequence C₁,…,C_M. Then

    d_H(s,b_j)=j,       d_H(s,a_i)=i.

For b_j, the displayed prefix has cost j. If another s-valid path to b_j had cost less than j, append the original s-valid suffix from b_j to t. That suffix visits M−j+1 chains, and both pieces contain C_j. Thus their union has cost at most the replacement-prefix cost plus M−j, strictly less than M, a contradiction. The proof for a_i is identical. Additional chain overlap only improves this upper bound.

This is fixed-source prefix optimality, also supplied by ChainEntries.minimum_takeUntil. It does not assert optimality after changing s to a_i.

Each b_j is the original entry e(s,C_j), and each later b_j is also e(a_i,C_j): the subpath makes b_j reachable from a_i, while any earlier a_i-reachable vertex of C_j would also be s-reachable. Hence the relevant rebased pairs are important.

## 2. One bad window pair gives a smaller charge set

Suppose the current important pair is (s,t), the current actual minimum has M≥L/2 chains, and a window pair satisfies

    1≤i≤k,  M−k+1≤j≤M,  δ=d_H(a_i,b_j)<4k.

Because K≥L, we have k≤L/64. Thus

    i+δ < 5k ≤5L/64 < M−k+1 ≤j.

By §1, this is a genuine strict failure of the triangle comparison

    d_H(s,a_i)+d_H(a_i,b_j) < d_H(s,b_j).

Apply ChainGuard.distance_guard_dichotomy with target b_j and pivot a_i. It yields an original-source important guard z such that

    s reaches z,   z reaches b_j,   a_i does not reach z,
    d_H(s,z) ≥ j−δ+1 ≥ M−5k.

(The displayed lower bound deliberately wastes the harmless integer slack.) Since b_j reaches t along P, z reaches t.

There is actual nestedness of charge sets:

    E_s(z) ⊆ E_s(t).

Indeed every original entry that reaches z also reaches t. Moreover, every entry b_h with h>i belongs to E_s(t) but not E_s(z). The pivot a_i reaches b_h by the suffix of P and legality of the augmented edges. If b_h reached z, then a_i would reach z, contradicting the guard property. The b_h are distinct actual vertices, one per chain. Therefore

    |E_s(t) \ E_s(z)| ≥ M−i ≥ M−k.

In particular, this argument counts entries only once across a recursive same-source target sequence: its charge sets are nested. It does not count conceptual guard-tree nodes as graph vertices. Any future path or future charge set lies in E_s(z), so previously removed entries cannot return.

This is stronger bookkeeping than merely counting off-path entries of one guard path. The latter supply sets can overlap across different failures. The permanent deletion sets above, along one nested lineage, cannot.

## 3. Exact stopping argument

Start from t₀. At each stage choose any actual minimum path for the current important pair. If all its k-by-k end-window pairs have rebased distance at least 4k, stop. Otherwise choose any bad pair and perform the guard replacement in §2. The source s and original entry map remain unchanged throughout.

Assume for contradiction that the process makes

    R = floor(4K/L)+1

replacements. Since L≤K, we have R·L≤4K+L≤5K. Every replacement loses at most 5k in distance. For every integer r with 0≤r≤R,

    M_r ≥ L−5kr,
    5kR ≤ (5L²/(64K))·(4K/L+1)
         = 20L/64 + 5L²/(64K)
         ≤ 25L/64.

Hence all current distances used in these R steps are at least 39L/64, in particular greater than L/2. This verifies inductively every hypothesis needed in §2; there is no assumption that the distances decrease monotonically.

At each replacement the number of permanently removed entries is at least

    M_r−k ≥ L/2−L/64 = 31L/64 > L/4.

The R successive deletion sets are pairwise disjoint because E_s(t_r) is nested. Their total cardinality is therefore greater than

    R·L/4 > K,

contradicting that all these vertices belonged to the initial K-element set E_s(t₀).

The process must consequently stop before R replacements. At its stopping state M≥L/2, and all the required old-distance window inequalities hold. This proves the structural assertion. It does not require favorable tie-breaking: choosing arbitrary actual minima and arbitrary bad pairs at each unsuccessful stage still terminates as above.

The small-k condition is explicit. If L²<64K, this theorem asserts no positive-size rectangle; k=0 is not promoted to a meaningful result. Since k≥1 implies L≥64, all window-separation and distinct-endpoint requirements used below are automatic.

## 4. Direct rectangle accounting

At the stopping state set h=M−k+1, and add e=(a_k,b_h). Since k≤L/64 and M≥L/2, the two chain windows are disjoint and h>k. The original augmented path supplies original-G reachability a_k→b_h, so e is legal and its endpoints are distinct.

Take source set U={a₁,…,a_k} and target set T={b_h,…,b_M}. Both sets have exactly k distinct vertices. For each i≤k and j≥h, (a_i,b_j) is an actual important pair, as proved in §1; also b_h is the original earliest entry on its chain reachable from a_i, so the new edge is allowed in the a_i-filter.

Follow P from a_i to a_k, then e, then P from b_h to b_j. Subpath validity under source rebasing is inherited (ChainSubwalk), and the later suffix is also valid in the fixed a_i-filter by earliest-entry inheritance. The resulting path uses at most

    (k−i+1) + (j−h+1) ≤ 2k

distinct chains. Uncovered vertices add no cost. No actual rebased minimum-path incidence is assumed: this is just a valid new upper-bound route.

The old distance is at least 4k. Hence every one of the k² distinct important pairs has actual saving at least 2k. Distances of all other important pairs are nonincreasing. ChainRectangleCharging.rectangle_drop_lower_bound therefore gives

    potential(H)−potential(H∪{e}) ≥ k²·2k = 2k³.

For example, if L²≥128K, then k≥L²/(128K), yielding the explicit bound

    potential drop ≥ L⁶/(2²⁰ K³).

This is a direct rectangle in the real raw potential, not an assumed progress certificate.

## 5. What this does and does not say about the logarithmic candidate

Let b=ceil(log₂(n+1)). If the relevant interval-entry count happens to satisfy K≤A·L·b for a fixed A, the theorem gives k of order L/(A b), subject to its explicit floor/nonzero condition, and M≥L/2. Thus in this restricted low-volume regime it gives exactly the useful end-window weakening at logarithmic scale, and a direct drop of order L³/(A³b³). It still does not assert the original stronger requirement concerning every half-length subpath.

In general K may be much larger than L·b. The justified recursion removes an additive amount of order M entries per step, while losing at most an amount of order k in distance. Balancing the number of possible steps, of order K/L, against the available distance L yields k of order L²/K. Replacing this with k of order L/b would spend too much distance when K≫L·b.

The interval inclusion alone is not a halving statement. A pivot descendant slice can account for only a small fraction of the current interval-entry set. The guard can retain almost all other entries. The proved off-path supply does not make the retained sets of two sibling recursions disjoint, and guard/shortest-path branches can merge. A hypothetical guard tree therefore cannot be assigned 2^depth distinct graph vertices without an additional structural argument.

For the original all-long-subpaths candidate, a bad interval may end as early as j≈M/2. The same guard bound only preserves M'≥M/2−δ, which is even weaker than the near-preservation obtained from end windows. The end-window weakening is the appropriate direct-rectangle target for this depletion argument.

Thus the precise remaining bottleneck is to improve additive interval-entry depletion into enough multiplicative shrinkage, or obtain equivalent controlled branching with proven disjoint charge sets, while preserving a distance of order L/log n. This report does not provide that improvement. The L²/K theorem alone neither repairs the paper's unsupported cubic assertion nor reaches its final near-linear greedy-stage target.
