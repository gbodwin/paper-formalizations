# A stretched symmetric family refutes constant-factor heredity on exact maximum paths

Date: 2026-10-10. This note analyzes a proposed repair of the hereditary-optimality argument in [arXiv:2511.20111v2](https://arxiv.org/abs/2511.20111v2), Lemma 5.7. The proof below is an ordinary mathematical argument with a finite diagnostic checker; it is not a Lean theorem.

## Result and its limits

The proposed assertion is false for every universal positive constant: there is an explicit family with a unique globally maximum important pair of distance L, exactly two minimum valid paths for that pair, and, on each path, a rebased important subpath of chain cost L−1 whose minimum normalized distance is exactly 3. The ratio 3/(L−1) tends to zero.

This is an asymptotic counterfamily, not just a finite obstruction to a selected numerical constant. It also respects the proposed endpoint restriction: the offending subpath starts at the last vertex of a singleton chain and ends at the first entry of the terminal singleton chain.

Two distinctions are essential:

1. The same family has fully hereditary minimum valid paths for important pairs of distances L−1 and L−2. It therefore does **not** refute replacing “globally maximum pair” by “some pair within a fixed fraction of the maximum.” That general variant remains unresolved in this investigation.
2. The family admits a legal edge with cubic raw-potential decrease. An explicit rectangle gives a lower bound asymptotic to L³/27. Thus it is **not** a counterexample to the paper’s cubic-progress conclusion, and it does not preclude a proof using a suitable sparse family of subpaths.

## 1. Explicit graph and chain family

Fix an integer m≥2. The vertices are

- a root r and a terminal t;
- arm vertices a_1,…,a_m and b_1,…,b_m;
- four tail vertices x_A,y_A,x_B,y_B.

The graph has precisely the edges along the two full arms

    r → a_1 → … → a_m → x_A → y_A → t,
    r → b_1 → … → b_m → x_B → y_B → t,

and the two cross edges

    a_1 → y_B,       b_1 → y_A.

The chains are the singleton sets {r}, {t}, {a_i}, {b_i}, and the two ordered chains

    C_A = (x_A,y_A),       C_B = (x_B,y_B).

There are 2m+6 vertices and 2m+4 chains. The graph is a DAG: the order

    r, a_1,b_1, a_2,b_2, …, a_m,b_m, x_A,x_B,y_A,y_B,t

is topological. Every vertex is covered. The only nontrivial within-chain forward pairs are already graph edges, so the consecutive-edge and at-most-four-hop preprocessing requirements hold with one hop. The graph needs no additional preprocessing edge. At m=2 this is exactly the earlier ten-vertex symmetric example, up to the displayed vertex names.

If the numerical 2n^(2/3)-chain-cover condition is required, let h=2m+4 and pad the graph to n=h² vertices with isolated **uncovered** vertices. This does not change any important pair or normalized distance in the core and introduces no new important pairs. Every path has at most one uncovered vertex; h≤2n^(2/3) and 1≤n^(1/3), so this is a valid 2n^(2/3)-chain cover under the paper’s definition. Moreover (m+3)³>(2m+4)², so L=m+3 remains above the algorithm’s n^(1/3) stopping threshold after this padding. This padding is a mathematical construction, not a modification to the algorithm or objective.

The definition of a chain cover and Algorithm 2 in Section 5 impose no lower bound on individual chain cardinalities.

## 2. Maximum distances and all maximum minimizers

For source r, the earliest reachable vertices of C_A and C_B are x_A and x_B. Consequently, either cross-edge path from r to t is invalid: it first enters the opposite tail chain at y rather than x. Exactly two r-valid paths reach t, namely the two full arms. Each visits

    1 root chain + m arm chains + 1 tail chain + 1 terminal chain = m+3

chains. Thus d′(r,t)=m+3.

For completeness, the important distances from every possible source are as follows; the b-arm statements are symmetric to the a-arm statements.

- From r: d′(r,r)=1; d′(r,a_j)=d′(r,b_j)=j+1; d′(r,x_A)=d′(r,x_B)=m+2; d′(r,t)=m+3.
- From a_1: d′(a_1,a_j)=j; d′(a_1,x_A)=m+1; d′(a_1,y_B)=2; d′(a_1,t)=3. Here y_B, not x_B, is the important entry of C_B, since a_1 cannot reach x_B.
- From a_i for 2≤i≤m: d′(a_i,a_j)=j−i+1 for j≥i; d′(a_i,x_A)=m−i+2; d′(a_i,t)=m−i+3. The opposite arm and its tail chain are unreachable.
- From x_A or y_A: the important distance to that source’s own earliest tail-chain entry is 1, and the important distance to t is 2.
- From t: the sole important distance is d′(t,t)=1.

These formulas follow from the displayed edges: every listed path to an arm vertex or early tail vertex is the unique directed path to that target; the only additional a_1-to-t path is the three-chain cross-edge path. In particular every non-root source has maximum important distance at most m+1. Therefore

    L = m+3,
    the unique maximum important pair is (r,t),
    and its only minimum valid paths are the two full arms.

All costs include the source chain, exactly as in the question.

## 3. Long subpaths with vanishing rebased ratio

Consider the A-arm maximum path. Its subpath

    Q_A = a_1 → … → a_m → x_A → y_A → t

has chain cost m+2=L−1. But

    a_1 → y_B → t

is an a_1-valid path of chain cost 3: the earliest a_1-reachable vertex of C_B is y_B. There is no a_1-to-t edge, and every a_1-to-t path has a source singleton, some other chain, and the terminal singleton. Thus the rebased minimum is exactly

    d′(a_1,t)=3.

The B-arm minimum path has the symmetric witness. In each case the pair is important, the subpath has at least L/2 chains, and its endpoints satisfy the proposed last-vertex/earliest-entry restriction. Hence every maximum minimum path fails any fixed positive-alpha guarantee once m is large enough:

    d′(Q.start,Q.end) / count(Q) = 3/(m+2) → 0.

Given any α>0 and threshold L_0, choose m≥2 with m+3≥L_0 and m+2>3/α. Then neither of the only maximum minimum paths has the requested property. This establishes the full quantifier-level refutation of the proposed exact-maximum-path assertion.

## 4. Near-maximum hereditary paths still exist

The important pair (r,x_A) has distance m+2=L−1. Its unique directed path

    r → a_1 → … → a_m → x_A

is fully hereditarily minimum under source rebasing: every subpath is the unique directed path between its endpoints. No cross edge can reach x_A or an earlier A-arm vertex. The same holds for (r,x_B).

Moving one vertex farther into either arm gives another near-maximum hereditary path. For m≥2, the important pair (a_2,t) has distance m+1=L−2, with unique directed path

    a_2 → … → a_m → x_A → y_A → t.

It and every subpath are unique directed paths and therefore minimum valid paths. The B-arm version is identical.

In fact the L−1 hereditary path is a prefix of one of the original maximum paths. Thus this obstruction is quite compatible with a proof that discards a short suffix, selects a slightly shorter important pair, or identifies only a sufficient rectangle of subpaths. No general result asserting that such a repair always exists is established here.

## 5. Explicit cubic raw-potential decrease

Choose integers 1≤p<q≤m with q≥p+2. Insert the legal closure edge

    a_p → a_q.

For every i≤p and j≥q, (a_i,a_j) is an important pair because a_j is a singleton chain. The old distance is

    d′(a_i,a_j)=j−i+1.

The edge gives the source-valid path

    a_i → … → a_p → a_q → … → a_j,

whose chain cost is

    (p−i+1)+(j−q+1) = j−i+2−(q−p).

Every visited chain in this replacement is a singleton, so no earliest-entry issue arises. Consequently each of the p(m−q+1) distinct important pairs decreases by at least q−p−1. Every other important distance is nonincreasing under the legal insertion, with original selectors fixed. For the exact raw-sum potential φ,

    φ(old)−φ(new) ≥ p(m−q+1)(q−p−1).

Taking p=floor(m/3), q=floor(2m/3) gives

    liminf_{m→∞} max_legal_edge_drop / (m+3)³ ≥ 1/27.

This is a lower bound for this family, not a universal bound or a claim about the exact best edge. Isolated uncovered padding leaves the potential calculation unchanged.

## 6. Finite independent checks

The adjacent script `verify-stretched-symmetric-obstruction.py` was run successfully for m=2,3,4,8,16,32,64,128. Its output is saved in `stretched-symmetric-obstruction-checks.json`.

The checker reconstructs reachability and original earliest entries, computes all source-dependent normalized minima by DAG dynamic programming, verifies the unique maximum pair and both maximum minimizers, checks the offending subpaths and all subpaths of the L−1/L−2 hereditary paths, and verifies the explicit edge’s raw-potential decrease. The DP is valid for this family because no path can leave and re-enter a chain, before or after the tested shortcut; transition cost is therefore exactly the number of distinct visited chains.

For example, at m=128, L=131, both offending subpaths have cost 130 and rebased distance 3. The middle-arm edge has actual raw-potential drop 83,034; the proved rectangle lower bound is 77,616. Finite checks support the symbolic proof above; they do not substitute for the all-m argument.
