# The existential hereditary-maximum-path repair is false

Date: 2026-10-10. Scope: a bounded mathematical diagnostic for the proposed repair of Lemma 5.7 in arXiv:2511.20111v2. This is not a counterexample to the lemma's final greedy potential bound.

## Exact candidate refuted

Let `G` be a finite DAG, with vertex-disjoint reachability chains `C` whose internal consecutive edges have been inserted and whose forward distances are at most four. Reachability is reflexive. For every reachable source–chain pair, let `e(s,C)` be its earliest reachable vertex, and let `S = {(s,e(s,C))}`. A path is valid relative to its first vertex when its intersection with every visited chain is contiguous and starts at that source's earliest reachable vertex of the chain. Its cost is the number of distinct chains it meets, including its source's chain when covered. Let `d'(s,t)` be the minimum valid-path cost and `L = max_{(s,t) in S} d'(s,t)`.

The candidate asserts that there exist `(s,t) in S` and a valid `s`–`t` path `P` such that:

1. `cost(P) = d'(s,t) = L`; and
2. for every subpath `P[u..v]` with `(u,v) in S`, `cost(P[u..v]) = d'(u,v)`.

The following graph refutes this assertion.

## Ten-vertex construction

Vertices are `0,1,...,9`, in topological order. The edges are exactly the union of these two paths and two additional edges:

- `0 → 1 → 3 → 5 → 7 → 9`
- `0 → 2 → 4 → 6 → 8 → 9`
- `1 → 8`
- `2 → 7`

The chains are `{5,7}`, `{6,8}`, and the six singleton chains `{0}`, `{1}`, `{2}`, `{3}`, `{4}`, `{9}`. All vertices are covered. Both nontrivial chains already have their consecutive edge, so their forward hopbound is one, stronger than the required four.

The chains are vertex-disjoint and totally ordered by reachability. There are eight chains and `8^3 = 512 ≤ 8·10^2 = 800`, equivalently `8 ≤ 2·10^(2/3)`. The uncovered-vertex condition is vacuous.

For a version with an exactly integral algorithmic parameter, add 17 isolated, unchained vertices. Then `n=27`, `ell=2·n^(2/3)=18`, there are at most 18 chains, and every path meets at most one uncovered vertex, which is at most `2n/ell=3`. No new important pairs are introduced, so all conclusions below remain unchanged. Thus the construction can satisfy the literal integer chain-cover convention without rounding.

## Hand verification

For source 0, the earliest vertices of the two nontrivial chains are 5 and 6. Consequently the paths `0→1→8→9` and `0→2→7→9` are invalid: they enter one of these chains after its earliest reachable vertex.

There are exactly four ordinary `0`–`9` paths. The two long displayed paths are the only valid ones, and both touch five distinct chains. Therefore `d'(0,9)=5`.

The maximum important-pair distance from each source is:

- source 0: 5;
- sources 1, 2, 3, 4: 3;
- sources 5, 6, 7, 8: 2;
- source 9: 1.

For source 0, its other important targets are `0,1,2,3,4,5,6`, with respective distances `1,2,2,3,3,4,4`. Hence `L=5` and `(0,9)` is the unique maximizing important pair.

On `P_A = 0→1→3→5→7→9`, the subpath from 1 to 9 has cost four. The pair `(1,9)` is important because `{9}` is a singleton chain. But `1→8→9` is valid relative to source 1: vertex 6 is not reachable from 1, so 8 is its earliest reachable vertex of `{6,8}`. This path has cost three, and no cost-two path exists. Therefore `d'(1,9)=3<4`.

Symmetrically, on `P_B = 0→2→4→6→8→9`, the subpath from 2 to 9 has cost four, whereas the valid path `2→7→9` has cost three. Here 7 is the earliest vertex of `{5,7}` reachable from 2. Thus `d'(2,9)=3<4`.

Every shortest valid path for the unique maximum pair fails the hereditary-shortestness requirement. The existential candidate is false.

Zero-length paths and self-pairs cause no ambiguity: for each covered vertex `v`, the path `[v]` touches one chain and has cost one. Omitting diagonal pairs from `S` would not change the maximum or the counterexample. In the padded graph, isolated uncovered vertices have no important source–chain pairs.

## Independent exhaustive check

`verification/verify-symmetric-existential-counterexample.py` enumerates all ordinary directed paths, tests the source-relative validity definition directly, counts distinct visited chains, and computes every important-pair minimum. It does not rely on the optimized normalized-distance dynamic program used in previous searches.

Its saved output is `verification/symmetric-existential-counterexample.json`. It confirms 33 important pairs, the unique maximum `(0,9)` with distance five, exactly two shortest valid paths for that maximum, and the two explicit subpath violations above. The coordinating worker independently obtained the same result using its separate dynamic program and shortest-path enumerator.

The graph is already an admissible current graph; zero additional closure insertions are a legal history. Every displayed edge respects the given topological order. The candidate was proposed for arbitrary legal current states, so a failure in this state suffices.

## Relation to the cubic-progress proof

The hereditary condition would be sufficient for the intended rectangle argument. On a hereditary shortest path touching `R` chains in order, write `a_i,b_i` for the first and last vertex of chain `i`. For indices `p<q`, insert the legal closure edge `b_p→a_q`. For every `i≤p` and `j≥q`, the pair `(a_i,a_j)` is important: earliest-entry validity inherits under source rebasing. The old distance is `j-i+1`, and the shortened path is valid and uses `j-i+1-(q-p-1)` chains. Distinct chosen prefix vertices and suffix chains give `p(R-q+1)` distinct pairs, each improving by at least `q-p-1`. Taking one-third/two-thirds cuts yields cubic progress up to rounding. A proved constant-factor-length hereditary path would similarly suffice asymptotically.

This report refutes the maximum-length existence assertion only. It does not refute existence of a constant-factor-length hereditary path or another way to prove cubic progress. Indeed this particular graph has initial potential 71; the coordinating worker's exhaustive closure-edge test finds a maximum one-edge drop of four, attained for example by `0→5`, so it does not violate the paper's stated weak numerical cubic lower bound. No weaker repair was pursued in this bounded pass.

No formal proof modules were edited or compiled for this diagnostic.
