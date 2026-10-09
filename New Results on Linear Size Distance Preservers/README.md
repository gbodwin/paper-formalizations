# New Results on Linear Size Distance Preservers

**Status: Theorems 1, 2, and 3 are proved in explicit finite forms.
Theorem 1 uses finite nonnegative weights. Theorem 3 covers every prescribed
vertex and terminal count in its range, with the necessary restriction
of at least two terminals. Theorem 4 remains incomplete.**
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
| Section 4 forcing step | `exists_shortest_of_distance_ne_top`, `forces_edges_of_unique_shortest`, and native weighted/unweighted forcing theorems | Attainment is proved for finite nonnegative weights; no shortest walk in the preserver is supplied |
| Theorem 5 displayed construction | `designated_not_shortest` | Refutes the displayed Euclidean-weight construction, not the existential theorem |
| Corrected Theorem 5 construction | `canonical_shortest`, `canonical_unique`, `canonical_isPath`, `canonical_edge_owner_unique`, `canonical_incidence`, and `subset_preserver_edge_count` | Actual finite undirected graph, positive symmetric weights, and list-based infimum distances; replacement weights below |
| Lemma 7 graph and unweighted metric | `ObstacleProduct.graph`, `fullWalk_unique`, `preserver_edge_count`; `factor_left_right` proves native walk decomposition | Unique input paths imply unique product paths and force every edge; the input conditions concern the actual inner graph and two-edge outer routes |
| Weighted obstacle product | `separated_optimal`, `ModularObstacle.full_optimal`, `preserver_eq` | Integer scaling discharges the product metric for the repaired modular inputs; all walks are covered, including backtracking. The generic finite epsilon lemmas also remain available |
| Theorem 6 finite graph and metric | `DirectionGraph.canonical_unique`, `convexPosition_rigid`, `graph_edge_count`, `canonical_edge_owner_unique`, `canonical_incidence` | Actual undirected vector graph; convex position gives unique shortest paths, edge ownership, exact counts, and regular incidence. Sharp direction-set existence/cardinality remains |
| Theorem 3 | `TheoremThree.bounded_range_lower_bound` | Every `C≥1`, `2≤T≤N`, `T³≤C³N²`: actual graph on `Fin N`, exactly `T` terminals, finite positive symmetric weights, and `T³N²≤(32768C)³E³` for every subset preserver. No construction inputs remain |
| Theorem 4 finite product | `DirectionObstacle.subset_preserver_edge_count`, `vertex_count`, `terminals_card` | Both product metric hypotheses are discharged from explicit bounded convex-position direction families. Sharp lattice construction/cardinality and global parameter selection remain; Theorem 4 is not proved end to end |

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
construction while preserving the relevant sizes. Its metric use inside the
obstacle product is now proved, as described below.

## Lower-bound extension

`ModularDistance.lean` defines `ModularGraph.graph` as an undirected
`SimpleGraph`, assigns finite positive symmetric weights, and encodes every
native walk (including backtracking) into the previously checked modular
walk datatype. `WalkSequence.lean` proves exact correspondence with lists;
it does not erase vertices or edges when converting a simple-graph walk.
`WeightedNativeForcing.lean` connects native cost minimization to the same
infimum distance used by Theorem 1.

The resulting `ModularGraph.subset_preserver_edge_count` is unconditional
apart from the construction's explicit finite parameters. For `n>0`,
`(k+1)x ≤ n`, and any `H ≤ ModularGraph.graph n k x`, preserving all
distances between the first and last layers forces

```
|E(H)| = knx.
```

The graph has `(k+1)n` vertices and, when `k>0`, exactly `2n` terminals.
Each designated route is a simple unique shortest native path, every edge
has exactly one route owner, and every vertex lies on exactly `x` indexed
routes. When `k>0`, `canonical_support_injective` proves that these routes
are distinct; no such distinctness assertion is made for a single layer.
Neither shortest-path attainment in `H` nor an edge-count hypothesis is an
input. This completes the metric interpretation of the repaired finite
Theorem 5 building block; it does not give Theorem 3's stronger bound by itself.

`ObstacleCounting.lean` constructs the actual substitution graph on
`A ⊕ ((B × U) ⊕ C)`. Middle vertex `b` gets its own copy of the inner vertex
type `U`; path label `j` selects the two ports. Its inputs express the
edge-disjointness of the input route systems. It proves

```
vertices = |A| + |B||U| + |C|
edges    = |B||J|(k+2).
```

Every indexed edge is on a constructed native substituted route. Layer
increments show those routes have minimum unweighted length `k+2`.
`preserver_edge_count_of_unique` is the original conditional reduction.
`ObstacleWalks.fullWalk_unique` now discharges product uniqueness from the
input path hypotheses, and `preserver_edge_count` applies it to arbitrary
unweighted distance-preserving subgraphs.
`ModularObstacle.data` constructs all structural inputs from the modular
inner graph and modular outer ports, with no edge-disjointness assumption
left to the caller. For `x≤n` and `nx≤σ`, the instantiated graph has
`2σ+σ(k+1)n` vertices and `σnx(k+2)` edges.

Those structural bounds cannot imply perfect paths. The independent review
exhibited `n=2, k=1, x=1, σ=2`: port codes 0 and 1 occur, and the routes
with `(middle vertex, port code)=(0,0)` and `(1,1)` have the same outer
endpoints but use different copies. They cannot both be uniquely shortest
under any weights. This is a mathematical review example, not an additional
Lean counterexample theorem. `ModularObstacleMetric.lean` now supplies the
stronger bounds `(k+1)x≤n` and `3nx≤σ` and proves weighted uniqueness.
The structural `data` definition retains its broader, valid domain; no
metric conclusion is deduced from the structural bounds alone.

`ObstacleWalks.lean` counts connector traversals in an arbitrary native
walk. A route between the outer layers with at most two connectors stays
inside one gadget; the two port labels may initially differ. In the
unweighted case, equality in the layer bound forces every step forward,
so exactly two connectors occur. Unique two-edge outer paths fix the copy
and both ports, and unique inner paths then fix the whole route.

`ObstacleWeights.lean` proves the weighted version for its normalized
integer-weight inputs using integer separation.
Each connector has primary cost at least `C`, while every designated outer
route costs less than `3C`. Any competitor with no greater primary cost
therefore has at most two connectors and admits the proved decomposition.
The outer quadratic comparison fixes its copy and ports; the inner
quadratic comparison fixes its inner route. Multiplying primary weights by
an integer greater than every designated inner cost makes all strictly
worse outer routes more expensive, even if they save all inner cost.
This covers every native walk without a simple-path restriction.
`PathPerturbation.lean` retains the general finite epsilon argument, but the
concrete modular product does not need to invoke it.

`ModularObstacle.full_optimal` discharges those numeric and metric
hypotheses from `(k+1)x≤n` and `3nx≤σ`. The weight scale is
`M = k*(k*x²+1+x²)+1`; all graph-edge weights are finite, positive, and
symmetric. `TheoremThree.lean` proves that any subset preserver on the
`2σ` outer terminals must equal the entire graph and hence retain exactly
`σnx(k+2)` edges. The distance is the same list-walk infimum used elsewhere
in the package, with attainment proved internally.

For every `k≥0, x>0`, `TheoremThree.family_lower_bound` instantiates

```
n = (k+1)x
σ = 3(k+1)x²
N = 2σ + σ(k+1)n
T = 2σ
E = σnx(k+2)
T³N² ≤ 648E³.
```

This older family remains available. `TheoremThreeExact.lean` now proves
Theorem 3 for arbitrary prescribed sizes, including the floor and padding
losses. Its strongest exported statement is
`TheoremThree.bounded_range_lower_bound`:

```
C ≥ 1, 2 ≤ T ≤ N, T³ ≤ C³N²
⇒ ∃ graph G on Fin N, positive symmetric weights w, and |S| = T,
  ∀ H ≤ G preserving every S×S distance,
    T³N² ≤ (32768C)³ |E(H)|³.
```

Equivalently, every such preserver has at least `T N^(2/3)/(32768C)`
edges. Any fixed real constant in the paper's big-O range is bounded by
some positive natural `C`. `exact_size_lower_bound` gives the better
constant `8192` when `T³≤N²`. These are cubed integer inequalities in Lean;
no real-power or named asymptotic corollary is claimed.

`PreserverPadding.lean` embeds a rigid witness into `Fin N`, proves equality
of all old-vertex distances in every subgraph by homomorphisms and pullbacks,
and preserves the exact edge count. It enlarges the terminal set to exactly
`T`. `PathLowerBound.lean` proves that one endpoint pair in a path forces
all `N−1` edges. `LowerBoundParameters.lean` selects and checks the floored
product parameters above the path regime. The final theorem assumes no
rigidity, uniqueness, attainment, or edge-count bound.

The condition `T≥2` is necessary: with one terminal, the only required
distance is zero, and an edgeless subgraph preserves it. At `T=0` the
claimed lower bound is zero. Padding may add isolated vertices; the paper
does not require the witness graph to be connected. The proof uses the
verified quadratic repair, not the displayed Euclidean weighting.

`DirectionGraph.lean` constructs the actual undirected graph on
`Fin(k+1) × (D → ZMod n)` from bounded nonnegative integer directions.
`canonical_unique` proves that every native walk of length at most `k`
between a designated pair equals its constant-direction route. It derives
forward motion, telescopes coordinate differences, proves no wraparound,
and applies the geometric `AverageRigid` property. That property says an
average of allowed vectors equalling an allowed vector must be constant;
it does not assume a graph-distance result. `sphere_rigid` proves it for
common-sphere directions. `ConvexRigidity.lean` proves the general bridge
from the ordinary convex hull of the other directions: a nonconstant
average can be stripped of repetitions of its target to express the target
as a convex combination of the rest. The paper's stronger prohibition of
combinations whose coefficients sum to at most one implies this condition.

`DirectionPerfect.lean` proves exact finite counts and ownership for
injectively indexed directions: `(k+1)n^d` vertices, `n^d |J|` indexed paths,
`k n^d |J|` edges, exactly `|J|` paths through every vertex, and exactly one
canonical path owning each edge. For `k>0`, `canonical_support_injective`
proves the indexed routes are distinct actual paths; at `k=0` several
labels may give the same singleton path. It also proves that every preserving
subgraph retains the graph under average rigidity.

`DirectionObstacle.lean` constructs the actual unweighted product from an
inner direction family `v : J → D → ℕ` and an outer family indexed by the
inner paths, `z : ((D → ZMod n) × J) → Q → ℕ`. Both are injective,
coordinate-bounded, and in convex position. The no-wrap inequalities are
`(k+1)r≤n` and `3R≤M`. These geometric inputs prove outer port uniqueness
and inner native-walk uniqueness. The product therefore has

```
vertices  = 2 M^|Q| + M^|Q| (k+1) n^|D|
terminals = 2 M^|Q|
forced edges = M^|Q| n^|D| |J| (k+2).
```

`subset_preserver_edge_count` quantifies over every subgraph preserving
all distances between those terminals, using mathlib's `SimpleGraph.edist`.
The two direction families remain inputs to that earlier theorem. The new
construction below supplies them from numerical conditions.

### Constructed directions and exact-size witnesses

`BehrendPorts` selects actual progression-free outer slopes from mathlib's
proved Behrend construction. The outer graph needs only two-term average
rigidity. Capacity `p ≤ R exp(-4 sqrt(log R))` suffices; the integer version
uses `p(q(b-1)²+1) ≤ b^q` with `R=(2b-1)^q`.

`SphereDirections` constructs exactly `x` distinct directions in the integer
box of side `r`, on one sphere, when `x(d(r-1)²+1) ≤ r^d`, and proves average
rigidity. `UnweightedPadding` preserves native `edist` constraints and the
forced edge count under injective padding and terminal enlargement.

`BehrendProduct.integer_lower_bound` constructs a graph on `Fin N` with
exactly `T` terminals, assuming only positive `n,M` and

```
x(d(r-1)²+1) ≤ r^d
(k+1)r ≤ n
3(2b-1)^q ≤ M
(n^d x)(q(b-1)²+1) ≤ b^q
2M + M(k+1)n^d ≤ N
2M ≤ T ≤ N.
```

Every subgraph preserving all terminal distances has exactly
`M n^d x (k+2)` edges. Both direction sets and all uniqueness properties are
proved internally. `sphere_lower_bound` gives the exponential-capacity version.

`UnweightedClique.clique_lower_bound` supplies the complete-graph baseline:
for every `1 ≤ T ≤ N`, an actual graph on `Fin N` with exactly `T` terminals
forces exactly `T.choose 2` edges in every subset preserver. It uses native
`edist` and exact isolated-vertex padding. This covers target lower bounds
at most `T.choose 2`; it provides no superquadratic estimate.

`TheoremFourDense.displayed_bound_of_small_deficit` connects this baseline
to the literal displayed real-power expression. Put
`t=(2/3)log N-log T`. For `2≤T≤N`, `d≥1`, `K≥0`, and

```
0 ≤ t ≤ K sqrt(log N)
27K²/8 + log 4 ≤ c sqrt(log N),
```

it constructs an actual `N`-vertex unweighted graph with exactly `T`
terminals whose every subset preserver has at least
`N^(2/(d+1)) T^((2d+1)(d-1)/(d(d+1))) exp(-c sqrt(log N))`
edges. The expression is at most `T²/4` in this regime, which the clique
witness supplies. This closes this explicit parameter range of the
displayed bound, not its superquadratic corollary or the remaining ranges.

**Full Theorem 4 remains incomplete.** The sphere estimate is roughly
`r^(d-2)/d`, weaker than the paper's `r^(d(d-1)/(d+1))` estimate. Sharp lattice
geometry, its dimensional constants, and parameter choices for the printed
rates remain open. Padding itself is now proved.

### Gap in the printed final implication

For `L=log N` and `t=(2/3)L-log sigma`, the logarithm of the displayed
polynomial factor divided by `sigma²` is

```
((3d+1)t-(2/3)L)/(d(d+1)) ≤ 27t²/(8L),  d≥1, L>0.
```

`TheoremFourRateAudit` proves this uniform inequality and connects it to the
literal log/real-power expression. If `0≤t≤K sqrt L`, including a uniform
loss `exp(-c sqrt L)` bounds that ratio by `exp(27K²/8-c sqrt L)`, which
tends to zero for fixed `K` and positive `c`. The pointwise inequality and
power correspondence are formalized; this last limit is not a separately
named Lean theorem. The bound is on a **lower-bound expression**, not on
graph edge counts. Thus the printed bound does not establish the stated
corollary; this is not a disproof of the existential graph theorem.
The independent skeptical reviewer confirmed this distinction and the gap.

## Verification

See [verification.md](verification.md) for the exact checks and scope.
The repository-wide commands build and audit all paper libraries:

```sh
lake build
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The axiom audit checks every declaration by its defining module, including
private and generated declarations. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. Every registered module root must contribute declarations.
