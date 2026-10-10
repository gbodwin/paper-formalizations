# Statement coverage and audit boundary

Source: Greg Bodwin, *New Results on Linear Size Distance Preservers*,
arXiv:1605.01106v4, 30 December 2020. Page numbers below are the printed
paper pages, not the PDF file's zero-based page numbers.

- PDF SHA-256: `0f579f4f454c145f435a1d51c6c5644da7f47303c7eddb42f720c331ee501f59`.
- TeX SHA-256: `aef731b5c31e9d2e1fc3bf426d2699fe82913608d3a9031fe1b141f538703e5b`.
- Canonical source: https://arxiv.org/abs/1605.01106v4
- Lean: `leanprover/lean4:v4.34.0`; mathlib:
  `5ed2965256430c3649e86755f9576b54eca72435`.

This inventory does **not** declare the entire original paper verified.
It separates finite proved conclusions, corrected constructions, and scope
that still needs proof or interpretation. The original paper text remains
unchanged in the companion Site. A fresh end-to-end independent audit gave a **qualified PASS for the corrected
package at `939a39a9`**, with the depth wording below corrected in this
documentation successor. [Read the audit](independent-audit-939a39a9.md).
This does not establish the still-unproved original claims.

## Uniformity follow-on after the qualified audit

The new nine-module follow-on closes the displayed growing-dimension rate
with an explicit uniform finite bound. It has separate component reviews and
verification gates; the earlier whole-package audit is not extended by this
addition. [Exact statement and proof decomposition](uniform-growing-dimension.md).
The original near-threshold existential assertion remains open.

## Main results

| Source statement | Actual formal conclusion | Coverage boundary |
|---|---|---|
| Theorem 1, p. 2: O(n+n^(2/3)p) directed weighted upper bound | `theorem_one`: for any finite directed adjacency relation, finite nonnegative weights, and p indexed demands, constructs a subgraph preserving the exact infimum walk distances, with at most `3n+24p floor(cuberoot(n))²` edges | No selection/attainment/consistency premises. Zero weights, loops, empty graphs, repeated demands, and unreachable pairs are included. Arbitrary signed weights or infinite edge weights are outside this theorem. The source does not explicitly state a signed-weight convention. The finite bound is the quantitative content; no separate named Big-O theorem is claimed. |
| Theorem 2, p. 2: O(p+n²/RS(n)) undirected unweighted upper bound | `theorem_two`: actual `H ≤ G`, native `SimpleGraph.edist` preservation, and `|E(H)| ≤ 2|P|+12 matchingNumber V`; `matchingNumber_subquadratic` gives the epsilon/threshold version of o(n²) | `matchingNumber` is an actual finite maximum for graphs partitionable into at most n induced matchings. The source's prose definition of RS reverses the implication used in its proof; the formalization uses the standard extremal interpretation. No unproved extremal estimate is a caller premise. Quantitative Fox/Behrend bounds quoted as background are not reproved here. |
| Theorem 3, p. 3: weighted Ω(σn^(2/3)) for σ=O(n^(2/3)) | `TheoremThree.bounded_range_lower_bound`: every fixed natural C>0, every `2≤T≤N` with `T³≤C³N²`, actual graph on `Fin N`, exactly T terminals, positive symmetric finite weights, and `T³N²≤(32768C)³ |E(H)|³` for every preserving subgraph | No geometric or metric construction premise. Requires at least two terminals, necessarily: one terminal's zero self-distance is preserved by an edgeless graph. Uses the verified quadratic-weight replacement of Theorem 5. The source little-omega corollary is now explicitly proved by `superquadratic_weighted_little_o`, using actual `IsLittleO` and `atTop`: for every admissible T(N)=o(N^(2/3)) and every real B, eventually actual exact-size witnesses force E>B*T². The companion finite theorem fixes B before N,T. |
| Theorem 4, p. 3: unweighted fractional-power lower bound | `TheoremFourGeneral.uniform_dimension_lower_bound`: for every real A>=0, N>=8, 2<=T<=N^(2/3), and integer 2<=d<=A sqrt(log N), actual exact-N, exact-T graphs force `N^(2/(d+1)) T^((2d+1)(d−1)/(d(d+1))) exp(-(1004+7A)sqrt(log N)) <= E` | No caller geometric or scale-selection premise. The constant is uniform in N,T,d after A is fixed. This includes the source displayed growing-dimension range. The separate near-threshold existential corollary remains unresolved. The older fixed-d theorem still covers every 2<=T<=N. |
| Theorem 4's “in particular” superquadratic assertion, p. 3 | `TheoremFourRateAudit.suppressed_expression_le` proves a dimension-uniform obstruction to deriving the asserted near-N^(2/3) range from the displayed rate with a uniform square-root exponential loss | This is a bound on the lower-bound expression, **not** a graph-edge upper bound and **not** a refutation of the existential assertion. The printed implication remains unsupported. The conservative finite replacement below is proved; it does not reach the printed range. |

### Proved fixed-exponent-gap superquadratic consequence

`TheoremFourGeneral.superquadratic_fixed_gap` gives the precise finite
statement: for each epsilon>0 and each real target factor B, there is a
natural N0 such that every N>=N0 and every integer 2<=T<=N^(2/3-epsilon)
admit an actual N-vertex unweighted graph with exactly T terminals whose
every subset preserver has E>B*T². The chosen dimension depends only on
epsilon; the eventual size threshold depends on epsilon and B. No asymptotic
oracle, uniform growing-d bound, or stronger source implication is used.
This is a valid superquadratic range below any fixed exponent less than 2/3;
it leaves the sharper printed near-threshold assertion above unresolved.

### Explicit fixed-d coefficient

`TheoremFourGeneral.displayed_lower_bound_explicit`, with d=n+3, replaces
K(d) by `rateFactor(explicitRadius(n),n+3)^(1/((n+3)(n+4)))`.
`explicitRadius` consists of the proved cap/volume constants and explicit
ceilings; its sharp vertex-count theorem has no caller-supplied geometric
premise. `UnitVolumeBounds` supplies elementary dimension-explicit cube
bounds for unit-ball volumes. No dimension-growth estimate sufficient for
the printed growing-d range is claimed by these statements.

### Conservative quantitative growing-dimension replacement

The new modules prove actual `explicitRadius<=d^(20d²)` and the graph-root
coefficient bound `<=d^(100d³)` for d>=3. There is no geometric premise.
`displayed_lower_bound_growing` has the same polynomial rate with
`exp(-5 sqrt(log N))` and coefficient one, provided
`100 d³ log d<=sqrt(log N)` and `2<=T<=N`.
`superquadratic_growing` additionally assumes `T<=N^(2/3-1/d)` and forces
`T² exp(sqrt(log N))<=E` in an actual exact-N, exact-T graph. N,T,d may vary
together under these explicit finite conditions.

`displayed_lower_bound_quantitative` covers every d>=3, 2<=T<=N without
the budget by retaining `exp(-4 sqrt(log N)-100 d³ log d)`.
`terminal_lower_bound_quantitative` converts a cap `T<=N^(2/3-epsilon)`
to the exact `T²`-normalized exponent
`((3d epsilon+epsilon-2/3)/(d(d+1)))log N-4 sqrt(log N)-100 d³ log d`.
It accepts any real epsilon; no positive-gain hypothesis is silently assumed.
These earlier quantitative statements alone did not cover the printed growing-d
range. The newer uniform theorem above now covers it. The sharper existential
assertion remains unresolved.

### Stronger corrected near-threshold range

The new `superquadratic_quarter_root` proves the same actual graph conclusion
`T² exp(sqrt(log N)) <= E` when `log N>=8^4`, `2<=T<=N`, and
`T<=N^(2/3) exp(-32(log N)^(3/4))`. Its eventual form fixes every real B
before a single N0, uniformly over all later N,T. All scales are internal.
[Exact theorem, reproduction commands, and review boundary](quarter-root-near-threshold.md).
This improves the older 5/6 deficit below; it does not reach the source
square-root deficit. These three modules have separate component review.

### Verified weaker near-threshold range

`TheoremFourGeneral.superquadratic_sixth_root` proves a clean finite
consequence with no user-supplied dimension: if `log N>=16^6`, `2<=T<=N`,
and

```
T <= N^(2/3) exp(-8 (log N)^(5/6)),
```

then an actual N-vertex graph with exactly T terminals forces
`T² exp(sqrt(log N)) <= E` for every terminal-distance preserver.
The proof chooses the actual integer `d=floor((log N)^(1/6)/4)` and checks
all rounding, coefficient, and radius-domain requirements.

`superquadratic_sixth_root_eventual` expresses the corresponding precise
superquadratic quantifiers: for every real factor B, there exists N0 such
that every N>=N0 and every admissible T in this range admits a graph whose
every preserver has `E>B*T²`. The factor is chosen before the eventual size
threshold, and T may vary with N. The numerical threshold above is coarse.

The intermediate `superquadratic_optimized_budget` gives a stronger
parameterized sufficient condition: d>=3, `T<=N^(2/3-1/d)`,
`200d⁵ log d<=log N`, and `12d²<=sqrt(log N)` imply the same explicit
`T² exp(sqrt(log N))` lower bound. No asymptotically optimized choice of d
for this stronger budget is claimed.

The exponent-5/6 deficit is larger than the source's printed square-root
logarithmic deficit. The latter existential assertion remains unresolved and is not refuted by
these results or by the separate displayed-expression obstruction. The displayed
uniform dimension range is now covered by the newer theorem above.

## Definitions and intermediate results

| Source item | Formal declarations / modules | Scope |
|---|---|---|
| Definition 1, p. 1: pair/subset preservers | `PathUnion`, `NativeWalkBridge`, `WeightedNativeForcing`; all final results quantify actual preserving subgraphs | Weighted infimum list-walk distances are bridged to native walks. Unweighted results use native extended distance including infinity. |
| Definition 2 and Lemma 1, p. 2: induced matchings, induced matching lemma | `InducedMatchings`, `InducedMatchingRemoval`, `matchingNumber_subquadratic` | Endpoint disjointness and all cross-edge exclusions are proved for each class. Tripartite triangle construction has no accidental triangles; actual imported triangle-removal theorem is applied. |
| Definitions 3–4 and Lemma 2, p. 4: consistent shortest paths | `ConsistentTiebreaking.exists_optimal`, `Optimal.shortest`, `optimal_subpaths_eq` | Deterministic lexicographic edge scores replace random perturbation; finite nonnegative weights and reachable endpoints. Unreachable demands are handled separately in Theorem 1. |
| Definition 5, Lemmas 3–4, pp. 4–5: branching triples and sparse union | `Branching`, `RoutingOfPaths`, `Batching`, `PaperTheorem` | Routing is built from actual selected shortest paths. The proved sufficient edge bound is `2n+p³`; batching yields Theorem 1. |
| Definitions 6–7 and Lemma 5, p. 5: lazy shortest-path trees | `LazyTreeSelection.exists_lazy_tree`, `tree_walk`, `tree_preserves`, `branchEdges_le_two_demands` | Tree selected by finite minimization. All nonroot leaves are demanded endpoints; demanded endpoints may also occur internally. Branching-edge bound at most twice demand endpoints. |
| Lemma 6, pp. 5–6: induced-matching partition | `exists_favorable_cut`, `LazyEdges.class_is_induced_matching`, `lazy_partition_bound` | Explicit finite averaging keeps a quarter; ownership resolves overlaps; three residue classes each use at most n induced matchings. |
| Definition 8, p. 7: perfect paths | `ModularDistance`, `DirectionPerfect`, `ObstacleCounting`, `ObstacleWalks` | Actual canonical native walks, unique shortestness, per-edge ownership, and exact incidence/counts. Indexed paths are proved distinct when the layer depth is positive. |
| Lemma 7, p. 8: obstacle product | `ObstacleWalks.fullWalk_unique`, `preserver_edge_count`, `FinitePerturbation`, `PathPerturbation`, `ObstacleWeights.separated_optimal`, `ModularObstacleMetric.full_optimal` | Unweighted finite product uniqueness and forcing are proved from actual input routes. A generic finite perturbation lemma is proved. The generic finite positive-real weighted metric join is now proved by `exists_real_weighted_product`, with one epsilon before all endpoint classes and competitors; `exists_real_weighted_forcing` gives actual native-distance forcing. Input simple-path uniqueness converts internally. No integer-weight, baseline or supplied gap premise remains. Strict positivity on actual input edges is explicit; zero, signed or infinite weights remain outside this generic theorem. See `generic-weighted-obstacle-product.md` for exact scope and separate verification stages. |
| Theorem 5, p. 8: weighted layered perfect paths | `WeightedConstruction.designated_not_shortest`; repaired `ModularGraph.Walk.optimal`, `canonical_unique`, `canonical_isPath`, `canonical_incidence`, `edge_count`, `subset_preserver_edge_count` | The printed Euclidean weighting has a kernel-checked counterexample. The same graph with slope weight `k*x²+1+a²` has the required metric properties. Conditions include positive modulus and `(k+1)x≤n`; positive depth is needed for distinct indexed paths. Literal unrestricted one-layer perfect-path incidence is not asserted. |
| Theorem 6, p. 9: unweighted layered perfect paths and sharp directions | `DirectionEncoding.exact_arbitrary_layer_size`: for each d>=2 one K>0, then every N>0,k>0,x>=0 under `((k+1)K)^(d(d−1)) x^(d+1)<=N^(d−1)`, actual (k+1)-layer graph with exactly N vertices per layer, kNx edges, distinct uniquely shortest canonical paths, incidence exactly x and unique edge ownership | Sharp direction supply and integer rounding are proved internally, including d=2 and x=0. Carry-free base encoding removes the perfect-power restriction on N without isolated padding. The source fixed-d exponent is retained in an exact finite power budget. At least two layers are required for the exported arbitrary-x distinct-path statement; the one-layer source degeneracy remains excluded. Scalar rigidity is only asserted at the needed path length. The stronger coefficient-sum-at-most-one convention in the source is neither assumed nor silently equated with average rigidity. [Details](theorem-six-exact-layers.md). |
| Referenced sharp lattice estimate, p. 9 | `LatticeMinima`, `LatticeDual`, `LatticeFlatness`, `LatticeCapGrouping`, `LatticeSliceVolume`, `LatticeSlicing`, `LatticeCellVolume`, `LatticeMissedVolume`, `PolytopeApproximation`, `LatticeApproximation`, `LatticeVertices` | Actual discrete lattices and Euclidean volume. No flatness, volume, facet, or vertex-count oracle remains. Covers d≥3; the graph theorem's d=2 case uses the independent primitive-direction construction. |
| Exact arbitrary sizes and ranges in lower bounds | `PreserverPadding`, `UnweightedPadding`, `LowerBoundParameters`, `PlanarParameters`, `HigherParameters`, `HigherRate`, `HigherBehrend` | Isolated-vertex padding, exact terminal enlargement, path/clique extremes, integer rounding, Behrend capacity, and fractional-power conversion are proved. No asymptotic rounding assertion substitutes for a finite proof. |

## Corrections and explicit exclusions

1. Theorem 5's displayed weights do not make every designated modular route
   shortest. At n=30 per layer, ell=3, x=10, the designated slope-9 path costs
   `2 sqrt(82)`; the checked simple competitor costs `4+2 sqrt(37)`.
   The quadratic repair proves the needed existential construction.
2. The RS prose definition is interpreted in the standard direction used by
   the induced-matching proof. The formal extremal quantity is fully defined.
3. At least two terminals are necessary for nonzero subset lower bounds.
4. No distinct-path incidence assertion is made in the degenerate one-layer
   case with several indexed labels. Distinct indexed inner canonical paths
   are asserted only under positive inner depth. Main obstacle-product
   parameter choices may allow zero inner depth; their full routes still
   have length k+2, and forcing does not require distinct inner singleton routes.
5. The new uniform-d Theorem 4 rate settles the displayed growing-d constants.
   It does not settle the printed final superquadratic existential assertion;
   that remains an explicit gap, with a formal obstruction for the current
   sharp-direction count family but no arbitrary-graph refutation.
6. Prior-work tables, literature bounds, and open questions are source
   context, not claimed newly formalized results. There is no proof of an
   open question and no invented axiom standing in for one.

Some earlier modules retain historical introductory comments describing the
sharp count as a future input. Their conditional theorem statements remain
valid intermediate lemmas; `LatticeVertices.uniform_vertices` now discharges
that input in `TheoremFourGeneral`. The current inventory and final theorem
types, rather than those historical comments, define the coverage claim.

## Reproducible verification

From the repository root, with the pinned toolchain and dependencies:

```sh
lake build
bash scripts/CheckModuleIndex.sh
lake env lean -DautoImplicit=false scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The axiom audit classifies every declaration by its defining module,
including private/generated declarations and alternative namespaces. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The kernel
replay script enumerates every source module; module-index checks detect
omitted imports. CI source SHA and logs must match the audited revision.
Local incremental checks are supplementary, not a substitute for exact-
commit CI or the independent semantic audit.

The adjacent `final-geometry-source-hashes.json` records every paper module's
SHA-256 and the input PDF/TeX hashes. Git commit/tree IDs and exact CI results
are recorded in the verification record after the run completes. A qualified independent end-to-end audit of the corrected package at
`939a39a9` passed. The original stronger claims remain explicitly unresolved.

## Post-audit construction-family obstruction

The new `ConstructionEnvelope` component proves a full-edge upper envelope
for the exact sharp-direction product count family. At a fixed K square-root
logarithmic terminal deficit, E<=2 T² exp(27K²/8), uniformly in d. This
excludes that family, even with ideal outer capacity, from yielding an
unbounded edge/terminal-square ratio. It does not upper-bound arbitrary
graphs or refute the original existential assertion.

[Exact assumptions and proof scope](construction-family-obstruction.md),
[exact-source component review](independent-construction-envelope-review.json).
All 91 audited mathematical modules remain byte-identical to 939a39a9. This
component and the later nine-module uniformity follow-on have separate gates
and component reviews. The whole-paper claim remains incomplete.

## Two additional checked consequences

The weighted Theorem 3 little-o consequence now has its own actual filter
statement and finite uniform factor theorem. A separate bounded-degree vertex
cover theorem proves linear density for the full-private-subdivision graph
shape. [Statements, domains and verification stages](weighted-corollary-and-subdivision-barrier.md).
Neither result resolves the original unweighted near-threshold existential gap.
