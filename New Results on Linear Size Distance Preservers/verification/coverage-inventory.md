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
unchanged in the companion Site. A fresh end-to-end independent audit is
required before any full-completion claim.

## Main results

| Source statement | Actual formal conclusion | Coverage boundary |
|---|---|---|
| Theorem 1, p. 2: O(n+n^(2/3)p) directed weighted upper bound | `theorem_one`: for any finite directed adjacency relation, finite nonnegative weights, and p indexed demands, constructs a subgraph preserving the exact infimum walk distances, with at most `3n+24p floor(cuberoot(n))²` edges | No selection/attainment/consistency premises. Zero weights, loops, empty graphs, repeated demands, and unreachable pairs are included. Arbitrary signed weights or infinite edge weights are outside this theorem. The source does not explicitly state a signed-weight convention. The finite bound is the quantitative content; no separate named Big-O theorem is claimed. |
| Theorem 2, p. 2: O(p+n²/RS(n)) undirected unweighted upper bound | `theorem_two`: actual `H ≤ G`, native `SimpleGraph.edist` preservation, and `|E(H)| ≤ 2|P|+12 matchingNumber V`; `matchingNumber_subquadratic` gives the epsilon/threshold version of o(n²) | `matchingNumber` is an actual finite maximum for graphs partitionable into at most n induced matchings. The source's prose definition of RS reverses the implication used in its proof; the formalization uses the standard extremal interpretation. No unproved extremal estimate is a caller premise. Quantitative Fox/Behrend bounds quoted as background are not reproved here. |
| Theorem 3, p. 3: weighted Ω(σn^(2/3)) for σ=O(n^(2/3)) | `TheoremThree.bounded_range_lower_bound`: every fixed natural C>0, every `2≤T≤N` with `T³≤C³N²`, actual graph on `Fin N`, exactly T terminals, positive symmetric finite weights, and `T³N²≤(32768C)³ |E(H)|³` for every preserving subgraph | No geometric or metric construction premise. Requires at least two terminals, necessarily: one terminal's zero self-distance is preserved by an edgeless graph. Uses the verified quadratic-weight replacement of Theorem 5. The displayed little-omega corollary follows mathematically from this finite inequality, but no separately named asymptotic-filter corollary is claimed. |
| Theorem 4, p. 3: unweighted fractional-power lower bound | `TheoremFourGeneral.displayed_lower_bound`: for every d≥2, there is K(d)>0 such that for every `2≤T≤N` an actual graph on `Fin N` and exactly T terminals force `N^(2/(d+1)) T^((2d+1)(d−1)/(d(d+1))) exp(−4(d−1)/d sqrt(log N)) ≤ K(d)|E(H)|` | The new geometry eliminates the previous sharp-count premise. The constant is dimension-dependent. No bound uniform for d growing with N up to O(sqrt(log N)) is established. Thus this is the full fixed-d displayed rate, not certification of all quantifiers in the source's growing-d statement. |
| Theorem 4's “in particular” superquadratic assertion, p. 3 | `TheoremFourRateAudit.suppressed_expression_le` proves a dimension-uniform obstruction to deriving the asserted near-N^(2/3) range from the displayed rate with a uniform square-root exponential loss | This is a bound on the lower-bound expression, **not** a graph-edge upper bound and **not** a refutation of the existential assertion. The printed implication remains unsupported; no replacement near-threshold theorem is claimed. |

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
| Lemma 7, p. 8: obstacle product | `ObstacleWalks.fullWalk_unique`, `preserver_edge_count`, `FinitePerturbation`, `PathPerturbation`, `ObstacleWeights.separated_optimal`, `ModularObstacleMetric.full_optimal` | Unweighted finite product uniqueness and forcing are proved from actual input routes. A generic finite perturbation lemma is proved. The full weighted metric join is established for the normalized integer-weight inputs used by Theorem 3, rather than a standalone arbitrary-real-weight version of every possible input graph. |
| Theorem 5, p. 8: weighted layered perfect paths | `WeightedConstruction.designated_not_shortest`; repaired `ModularGraph.Walk.optimal`, `canonical_unique`, `canonical_isPath`, `canonical_incidence`, `edge_count`, `subset_preserver_edge_count` | The printed Euclidean weighting has a kernel-checked counterexample. The same graph with slope weight `k*x²+1+a²` has the required metric properties. Conditions include positive modulus and `(k+1)x≤n`; positive depth is needed for distinct indexed paths. Literal unrestricted one-layer perfect-path incidence is not asserted. |
| Theorem 6, p. 9: unweighted layered perfect paths and sharp directions | `DirectionGraph.canonical_unique`, `DirectionPerfect`, `LatticeHull.exists_directions`, `LatticeVertices.uniform_vertices`; planar alternative `PrimitiveDirections`/`ConvexChains` | Actual finite box/lattice-hull directions with sharp fixed-d growth, no-wrap conditions, exact graph counts, and native metric forcing. Ordinary convex-position average rigidity suffices. The stronger coefficient-sum-at-most-one convention stated in the source is not assumed or silently equated with it. The source's all-n asymptotic formulation is represented by finite construction scales and exact final graph padding, not a separately named exact-per-layer theorem for every n. |
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
   case with several indexed labels. The actual constructions used in the
   main lower bounds have positive depth.
5. The fixed-d Theorem 4 rate does not settle uniform growing-d constants or
   the printed final superquadratic implication. These remain explicit gaps.
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
are recorded in the verification record after the run completes. No final
whole-paper audit has yet passed for this extension.
