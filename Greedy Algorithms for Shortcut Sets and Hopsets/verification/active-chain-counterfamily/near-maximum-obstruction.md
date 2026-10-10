# Active-regime obstruction to near-maximum hereditary repair

Date: 2026-10-10. Informal mathematical analysis of a proposed constant-factor near-maximum hereditary repair for the source-dependent normalized distance in arXiv:2511.20111v2, Lemma 5.7. This diagnostic is separate from the Lean formalization.

## Result and scope

**The proposed near-maximum hereditary assertion is false even in the active regime.** More precisely, for every α>0, every 0<β≤1, and every L₀, there is a finite DAG with legal chain preprocessing and H empty, with n vertices, at most 2n^(2/3) disjoint chains, at most n^(1/3) uncovered vertices on every path, and maximum important distance L≥L₀ satisfying L³>n, such that every minimum valid path for every important pair of distance at least βL contains an endpoint-restricted subpath Q with

    count(Q) ≥ count(P)/2,     d(Q.start,Q.end) < α count(Q).

The witnesses below start at the last vertex of the first tree chain and end at the original important endpoint. Thus they satisfy the requested endpoint restriction. For β>1 no pair can meet the requested distance threshold, so it cannot rescue the assertion.

This is a counterexample to this particular repair, **not a proof that the cubic one-edge progress bound, the phase bound, or the main shortcut theorem is false**. No upper bound on the best edge's raw-potential decrease is claimed here. The example is a legal empty-H initial state for the explicitly supplied cover, with all required internal preprocessing already present. It is not a claim that a particular chain-cover implementation must select this cover, nor a classification of states reachable after positive numbers of greedy insertions.

The key modification of the previously unverified binary-tree sketch is to fix its height and then stretch its upward edges by arbitrarily many singleton chains. Its exponential dependence on height no longer excludes the active regime. Cross edges must use siblings of **strict** ancestors; allowing siblings of the node itself would create directed cycles.

## 1. Explicit construction

Fix integers h≥4 and k≥1. Take a perfect binary tree of height h, oriented toward its root o; leaves have height 0. There are

    T = 2^(h+1) − 1

tree nodes. Replace each tree node v by a two-vertex ordered chain C_v=(x_v,y_v), with edge x_v→y_v. Introduce a separate vertex r in its own singleton chain, and edges r→x_v for every leaf v.

For every non-root tree node v, with parent p(v), replace its upward connection by

    y_v → z_(v,1) → ... → z_(v,k) → x_p(v).

Every z_(v,j) is its own singleton chain. Finally, for every node u and every strict ancestor a of u other than o, add

    y_u → y_b,    where b is the sibling of a.

These are all edges. There are

    M = 1 + T + (T−1)k                 chains,
    n_core = 1 + 2T + (T−1)k = M+T    core vertices.

The graph is acyclic: order r first, then successive height levels, putting x_v before y_v and the interiors of the v-to-parent edge after height(v) and before height(v)+1. Every cross edge increases height strictly. The only two-vertex chains already have their forward edge, so the required at-most-four-hop internal preprocessing is satisfied with one hop. Take H empty.

All core vertices are covered. Pad with isolated uncovered vertices to obtain exactly n=M² vertices. There are enough slots since M≥T+1 and M²≥M+T. This introduces no important pairs or changes to any core distance. Every original path contains at most one uncovered vertex. Moreover

    M ≤ 2(M²)^(2/3) = 2n^(2/3),     1 ≤ n^(1/3).

Thus this is a chain cover with the numerical parameters required in the question. No lower bound on individual chain cardinalities is used in the source's definition.

## 2. Reachability and source selectors

Write A(u) for the ancestors of u including u, and B(u) for the siblings of the strict ancestors of u other than o. Every node in B(u) lies outside A(u).

For a source s=x_u or y_u, the reachable vertices consist exactly of:

- its own chain from s onward;
- both vertices of every strict ancestor a of u;
- y_b, but not x_b, for every b∈B(u);
- all interiors z_(w,j) of upward edges whose bottom w is in A(u)∪B(u), excluding o which has no upward edge.

To verify this exactly: the ordinary upward path gives A(u) and its edge interiors. Each stated cross edge reaches y_b directly, then its upward edge returns to the ancestral path at p(b). No other reachable chain can be created afterward. Indeed, for a∈A(u), B(a)⊆B(u). For b∈B(u), every strict ancestor of b is an ancestor of u above p(b), and therefore B(b)⊆B(u). Thus the listed set is closed under every outgoing edge. It contains the source and all directly described routes, proving both inclusion directions. In particular x_b cannot be reached: reaching y_b does not permit movement backward inside C_b, and no listed route enters b through a child.

Consequently the earliest reachable chain vertices are s on its own chain, x_a on each strict ancestral chain, and y_b on each side chain b∈B(u). All other covered reachable vertices are singletons, whose selectors are tautological. This proves the original-graph filters used below, rather than assuming them from a drawing.

For an interior source s=z_(w,j), the only route out initially is the remaining portion of its upward edge to x_p(w). Before that endpoint the reachable chain vertices are precisely the remaining singleton interiors. Afterward the reachable set and selectors agree with those for source x_p(w). No vertex reachable from x_p(w) can return to that initial edge, by acyclicity.

For source r, every x_v is reachable by an ordinary path starting at a leaf below v. Hence its earliest entry on every C_v is x_v, and all singleton selectors are their vertices.

## 3. Bounds for every non-r source

For s=x_u or y_u, every important distance is at most 2k+3. The following explicit valid routes prove this claim for all reachable target types.

1. The own-chain important target is s, of cost 1.
2. The parent target x_p(u) has the ordinary route of cost k+2.
3. For an ancestor a at least two levels above u, let c be the child of a on the u-to-a ancestral path and let b be the sibling of c. Since c is a strict ancestor of u, the cross edge y_u→y_b exists. Use the source chain, that cross edge, the k interiors of b's upward edge, and x_a. This costs k+3. It is s-valid because e(s,C_b)=y_b and e(s,C_a)=x_a.
4. A side target y_b, b∈B(u), has the direct cross route of cost 2.
5. For an interior target z_(w,j) with w∈A(u), first reach the important entry of C_w by one of the above valid routes, move internally to y_w, and follow j singleton interiors. The cost is at most k+3+j≤2k+3 (and is smaller when w=u). This extension cannot revisit an earlier chain: all its new vertices are above w, and the explicit route to w ends there before entering its upward edge. Its singleton entries are automatically valid.
6. For an interior target z_(b,j) with b∈B(u), use the direct cross edge to y_b and then its j interiors, of cost 2+j≤k+2.

These cases exhaust the exact reachability list. They also apply to the source's last vertex y_u, not only x_u.

For s=z_(w,j), an important target on the remaining initial edge has distance at most k. For a target beyond x_p(w), concatenate the forced remaining singleton prefix, containing k−j+1≤k chains, with an x_p(w)-valid route of cost at most 2k+3. The source filters after x_p(w) are identical, and the chain sets of the two pieces are disjoint. Thus every important distance from any interior source is at most 3k+3.

Therefore every non-r source has every important distance at most 3k+3. Isolated uncovered padding vertices have no reachable chain and thus contribute no important pairs.

## 4. Exact root distances and all minimizers

No r-valid path can use a cross edge y_u→y_b: it would enter C_b at y_b even though e(r,C_b)=x_b. That chain cannot already have appeared on the path, since all previous vertices have lower height and C_b has strictly greater height than C_u. Thus every r-valid path is a leaf-to-ancestor ordinary upward route preceded by r.

For a tree node v of height ℓ,

    d(r,x_v) = ℓ(k+1)+2.

For an interior vertex on the upward edge from v of height ℓ,

    d(r,z_(v,j)) = ℓ(k+1)+j+2,    1≤j≤k.

These follow by counting the root singleton, ℓ+1 tree chains, ℓ complete stretches, and the j partial-stretch singleton vertices when present. Every possible r-valid path to one of these targets has exactly that form and cost; the choice of descendant leaf is the only variation. In particular these formulas describe **every** minimum path, not just a selected minimizer.

The root's largest important distance is attained at x_o and equals

    L = h(k+1)+2.

Since h≥4 implies L>3k+3, the all-source bound in §3 proves that this is also the global maximum important distance.

Let P be any minimum r-valid path of cost ell≥3, and let v be its first leaf. Delete the initial vertex r and the first leaf vertex x_v, retaining the subpath Q from y_v to P's endpoint. Because the leaf chain still appears through y_v,

    count(Q)=ell−1≥ell/2.

The starting point is the last vertex of that leaf-chain visit. The endpoint is either x_a, the first vertex on an ancestral chain, or a singleton interior vertex, so it is the first vertex of its final chain visit. It is also important relative to y_v, by the selectors in §2. The non-r bound for a tree-vertex source gives

    d(y_v,P.end) ≤ 2k+3.

For the long paths selected in §5, the endpoint lies on a later chain as required.

## 5. Quantifiers and active-regime inequality

Given α>0 and 0<β≤1, choose an integer h≥4 satisfying

    βh>6,      αβh>α+6.

Keep this height fixed. For every k≥1, the exact value L=h(k+1)+2 gives

    βL>6k≥3k+3,
    α(βL−1) > (α+6)k−α ≥ 6k > 2k+3.

(The first strict inequality makes the non-strict equality at k=1 harmless.) Consequently every important pair of distance at least βL is sourced at r. For every one of its minimum paths P, the Q in §4 satisfies

    d(Q.start,Q.end) ≤ 2k+3 < α(βL−1) ≤ α(count(P)−1) = α count(Q).

Also βL>6 ensures Q spans later chains and has at least half P's chain count. Thus there is no qualifying near-maximum minimum path with the proposed all-long-subpaths property.

It remains to impose L≥L₀ and L³>n without changing this conclusion. For k≥1,

    M=T+1+(T−1)k ≤ 2Tk,     L≥hk.

Choose any integer k large enough that hk≥L₀ and k>4T²/h³. Then

    L³ ≥ h³k³ > 4T²k² ≥ M² = n.

Such k exist arbitrarily large with h fixed. This proves the entire quantified counterfamily inside the active regime. The graph is explicit but not claimed to be the smallest obstruction.

## Remaining cubic-progress question

The obstruction refutes the proposed constant-factor near-maximum hereditary-path repair. It does not estimate the aggregate savings from the many sources on the stretched edges and the many side branches. Those sources can still support substantial rectangles of important pairs even when their maximum distances are small compared with L. A direct cubic-saving rectangle or a valid multiplicity/guard argument therefore remains an independent possibility. The paper's false hereditary-optimality sentence is not used anywhere in this construction or proof.

## Finite diagnostic check

The independent executable `check-active-tree-obstruction.py` recomputes original reachability, source-dependent earliest entries, and every important distance for nine small cores and the active padded cases (n,L)=(262144,70),(4194304,167). All checks pass; see `active-tree-independent-checks.json`. Only the covered cores are materialized, since isolated padding cannot change a core distance. The quantified claim rests on the symbolic proof, not the finite tests.

A separate companion note, `cubic-rectangle.md`, proves a cubic-saving rectangle for this very family. Thus the failure of the proposed hereditary repair does not prevent cubic raw-potential progress in these examples.
