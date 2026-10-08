# New Results on Linear Size Distance Preservers

**Status: Theorems 1 and 2 are proved end to end in explicit finite forms,
with finite nonnegative weights for Theorem 1. Theorems 3–4 remain incomplete.**
The package also contains a checked counterexample to one displayed weighted
construction and a verified replacement construction.

Source: Greg Bodwin, *New Results on Linear Size Distance Preservers*,
[arXiv:1605.01106v4](https://arxiv.org/abs/1605.01106v4), 30 December 2020.
The library is `LinearDistancePreservers`; run Lake commands from the
repository root. Lean and mathlib retain the repository's pinned versions.

## Main upper bounds

`theorem_one` in `TheoremOne.lean` takes only a finite vertex type, an
arbitrary directed adjacency relation, finite nonnegative edge weights, and
`p` indexed demand pairs. It constructs a subgraph preserving their exact
list-walk distances and proves

```
|E(H)| ≤ 3n + 24p floor(cuberoot(n))².
```

There is no shortest-path, attainment, consistency, or routing hypothesis.
Zero weights, self-loops, empty graphs, repeated demands, and unreachable
demands are covered; unreachable distances are infinity. Signed weights and
infinite edge weights are outside this unconditional theorem's scope. The
older theorem with extended nonnegative weights remains available as
`theorem_one_of_consistent_selection`, with its explicit selection inputs.

`theorem_two` in `TheoremTwo.lean` takes only a finite undirected simple
graph and a finite set `P` of demands. It constructs `H ≤ G`, preserves all
demanded `SimpleGraph.edist` values, including infinity, and proves

```
|E(H)| ≤ 2|P| + 12 matchingNumber V.
```

`matchingNumber V` is **defined** as the maximum edge count of a simple graph
on `V` partitionable into at most `|V|` induced matchings. It is not an assumed
bound. An edge set uses one orientation of each undirected edge, and
`InducedPartition` requires endpoint disjointness and exclusion of all cross
edges within each color class. This is the standard extremal quantity
`M(n) = n²/RS(n)` used in the paper's proof. The defining implication is
“a graph partitionable into n induced matchings has at most M(n) edges.”
The PDF's prose definition reverses this implication; we use the standard
extremal interpretation required by its proof.

`matchingNumber_subquadratic` proves the epsilon/threshold form of
`M(n) = o(n²)`. `InducedMatchingRemoval.lean` constructs the tripartite graph
with three vertex copies and one triangle per original edge, proves explicit
triangles are edge-disjoint and no accidental triangles exist, and applies
mathlib's `SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset`. This is an
actual use of the imported triangle-removal theorem, not a new axiom or an
unused import. Mathlib's separately named `ruzsaSzemerediNumberNat` counts
triangles in locally linear graphs and is not silently substituted for M(n).

## Proof map and remaining scope

| Paper component | Formalized result | Scope or interpretation |
| --- | --- | --- |
| Definition 1 | `PathUnion.lean` defines list walks, costs, and infimum distances; `NativeWalkBridge.lean` proves the native-walk correspondence | Theorem 1 uses exactly these distances; Theorem 2 uses mathlib's unweighted extended distance |
| Lemma 2 | `exists_optimal`, `Optimal.shortest`, and `optimal_subpaths_eq` in `ConsistentTiebreaking.lean` | Deterministic lexicographic minimization by original cost, then powers-of-two edge scores; finite nonnegative weights |
| Lemmas 3–4 and batching | `RoutingOfPaths.routing`, `routing_edges_iff`, and the existing branching/batching theorems | The routing is constructed from actual shortest paths; the sufficient bound is `2n+p³` |
| Theorem 1 | `theorem_one` | Unconditional within the weight model stated above; explicit rounded finite bound |
| Lemma 5 | `exists_lazy_tree`, `tree_walk`, `tree_preserves` | Minimizes tree size, then single-child parents; non-root leaves are demand endpoints. Endpoints lying inside other paths need not be leaves |
| Branching count | `branchEdges_le_two_demands` | At most twice the number of demand endpoints per tree |
| Lemma 6 | `exists_favorable_cut`, `class_is_induced_matching`, `lazy_partition_bound` | One-quarter survival proved by finite averaging; overlap resolved by assigning each edge one owner; three residue groups each have at most n classes |
| Induced Matching Lemma | `matchingNumber_subquadratic` | Explicit reduction to mathlib's triangle-removal theorem |
| Theorem 2 | `theorem_two` | No tree, cut, path, or extremal estimate is supplied as a hypothesis |
| Section 4 forcing step | `unique_shortest_forces_edges` | An attaining shortest walk in the subgraph is still an input to this older lemma |
| Theorem 5 displayed construction | `designated_not_shortest` | Refutes the displayed Euclidean-weight construction, not the existential theorem |
| Corrected Theorem 5 construction | `ModularGraph.Walk.optimal`, `unique_vertex_sequence`, incidence and edge counts | Replacement weights below; distinct indexed paths require at least two layers |
| Theorems 3–4 and Lemma 7 | Not formalized | Obstacle product, lower-bound parameter assembly, and unweighted convex-lattice construction remain |

Every listed proved result has a proof term. Missing lower-bound components
are not represented by custom axioms or admitted proofs.

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
