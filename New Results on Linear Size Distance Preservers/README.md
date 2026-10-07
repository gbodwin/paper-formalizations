# New Results on Linear Size Distance Preservers

**Status: a checked partial formalization, including a checked correction to
one construction. This is not an end-to-end formalization of all four main
theorems.**

Source: Greg Bodwin, *New Results on Linear Size Distance Preservers*,
[arXiv:1605.01106v4](https://arxiv.org/abs/1605.01106v4), 30 December 2020.
The library is `LinearDistancePreservers`; run Lake commands from the
repository root. Lean and mathlib retain the repository's pinned versions.

## Coverage

| Paper component | Formalized result | Remaining limitation |
| --- | --- | --- |
| Definition 1 | Directed weighted walks, extended nonnegative distance, and equality of distances for a union of selected shortest paths | Existence of a shortest selection is supplied, not constructed |
| Lemma 2 | Its predecessor/order consequence is the explicit `Routing` input | Consistent tiebreaking existence is not proved |
| Lemmas 3–4 | `branch_vertex_unique`, `excess_card_le`, and `edges_card_le` | Uses the sufficient bound `2n+p³`, not the sharper binomial coefficient |
| Theorem 1 batching | `integer_theorem_one`: at most `3n+24p floor(cuberoot(n))²` edges | Requires a `Routing`; `n>0` |
| Theorem 1 distance guarantee | `theorem_one_of_consistent_selection` combines the edge bound with subgraph containment and exact weighted distances | Explicitly conditional on consistent shortest paths and their edge correspondence; unreachable demands are not handled by the selected-walk input |
| Lemma 6 induced-matching step | `class_is_induced_matching` proves endpoint disjointness and absence of cross edges after a cut and depth-mod-3 partition | Lazy nonbranching tree edges and shortest-path depth labels are inputs |
| Theorem 2 | The deterministic induced-matching step only | Lazy-tree construction, favorable cut, branching count, and extremal-function bound are not yet formalized |
| Section 4 forcing step | A unique shortest path forces its edges into an equal-distance subgraph | A shortest walk attaining the subgraph distance is supplied |
| Theorem 5 displayed construction | `designated_not_shortest` proves an explicit counterexample to the stated Euclidean weighting | This refutes that construction, not the existential theorem |
| Corrected Theorem 5 construction | `ModularGraph.Walk.optimal`, `unique_vertex_sequence`, path-incidence and edge-count theorems | Uses the replacement weights below; distinct indexed paths require at least two layers |
| Theorems 3–4 and Lemma 7 | Not formalized | Obstacle product, asymptotic lower-bound parameterization, and unweighted convex-lattice construction remain |

All the listed proved statements have proof terms. No missing component is
represented by a custom axiom or an admitted proof. A conditional theorem is
still conditional after it passes the axiom audit: the audit does not remove
its explicit inputs.

## Construction issue: Theorem 5, printed page 8

Set the paper's parameters to `n=30` vertices **per layer**, `ell=3`, and
`x=10`. This is a 90-vertex undirected graph. The designated slope-9 path is

```
(0,0), (1,9), (2,18).
```

Its length is `2 sqrt(82)`. The following simple path has the same endpoints:

```
(0,0), (1,0), (0,24), (1,24), (0,18), (1,18), (2,18).
```

Its edge slopes are `0,6,0,6,0,0`, read from the lower layer toward the higher
layer. It has length `4+2 sqrt(37) < 18 < 2 sqrt(82)`.
`WeightedConstruction.lean` checks the parameter constraints, adjacency of
every step, simplicity of the competitor, equal endpoints, both exact costs,
and the strict inequality. It uses kernel-checked arithmetic, not numerical
approximations or `native_decide`.

The gap in the Euclidean argument is that a competing path may backtrack in
layer and wind around the column coordinate. Bounding the horizontal gain
of the designated forward path does not exclude such competitors.

## Verified replacement construction

Keep the same modular graph, with `k+1` layers, `n` columns, and slopes
`0 <= a < x`, assuming `(k+1)x <= n`. Replace the weight of slope `a` by

```
C + a², where C = k*x²+1.
```

Every constant-slope forward path is uniquely shortest. A longer walk costs
at least `(k+1)C`, which exceeds the designated cost. A walk with exactly `k`
steps must move forward throughout. The endpoint congruence then becomes
an equality of slope sums, and the sum of squared deviations proves that
equality of costs forces every slope to be `a`.

`ModularGraph.Walk` stores vertices in `Fin (k+1) × ZMod n`, directions,
slopes, and the local layer/column equations. The endpoint equations are
proved by telescoping these local equations. The proof therefore covers
arbitrary backtracking walks in the finite graph, not just monotone paths.
`unique_vertex_sequence` identifies the entire minimizing vertex sequence.

The construction has `(k+1)n` vertices, `nx` indexed designated paths,
exactly `x` paths through each vertex, and exactly `knx` undirected edges.
For `k>0` the path indexing is injective. Edge indexing by path and position
is injective as well, so each edge belongs to exactly one designated path.
The integer weights are positive. Thus this repairs the finite weighted
construction while preserving the relevant sizes. Its use inside the
obstacle product and the resulting Theorem 3 are still outstanding.

## Verification

See [verification.md](verification.md) for the exact checks and scope.
The repository-wide commands build and audit both paper libraries:

```sh
lake build
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The axiom audit checks every declaration by its defining module, including
private and generated declarations. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. Both module roots must contribute declarations.
