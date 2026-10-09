# Bodwin paper formalizations

Lean 4 formalizations of Greg Bodwin's papers, using mathlib.

## Bodwin–Patel: A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners

The implementation lives in the top-level [A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners](<A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners/>) folder.
Run the verification commands below from the repository root.

The VFT main theorem and Corollary 2 are proved end to end: the defined weighted greedy algorithm
returns a fault-tolerant spanner, constructs its small blocking set, and satisfies
explicit finite versions of Theorem 1 and Corollary 2. This is not yet a
formalization of every claim in the paper.

The main declaration is
`VFTSpanners.vft_greedy_theorem_one` in
[`PaperTheorem.lean`](<A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners/VFTSpanners/PaperTheorem.lean>).
For a finite simple undirected graph on `n` vertices, nonnegative real edge
weights, and integers `k ≥ 1`, `f ≥ 1`, its actual greedy output `H` satisfies:

- `H` is a subgraph of the input and uses the same edge weights.
- After any at most `f` vertex faults, every weighted distance is stretched by
  at most `k`, with disconnected distances represented by infinity.
- `|E(H)| ≤ 36 f² b(max(2, floor(n/f)), k+1)`, where `b(N,g)` is **defined** as
  the maximum edge count over all `N`-vertex simple graphs with girth greater
  than `g`.

The main theorem assumes neither a blocking set nor a favorable sample. Both
are constructed in the proof. The zero-fault case is proved separately.

For stretch `2r-1`, positive integers `r,f`, and `m = |E(H)|`,
`VFTSpanners.corollary_two` additionally proves
`m^r ≤ 72^r n^(r+1) f^(r-1)` together with the subgraph and distance guarantees.
This has **no Moore-bound hypothesis**. The new `Moore.lean` proves
`b(n,2r)^r ≤ 2^r n^(r+1)` by vertex pruning and short-path counting, with a
constant uniform in `n` and `r`. No additional external dependency is needed.

| Paper component | Status |
| --- | --- |
| Weighted VFT greedy algorithm and correctness | Proved |
| Equivalence of its walk test and shortest-distance test | Proved, including zero weights |
| Definition 3 and Lemma 3, small blocking set | Proved |
| Lemma 4, cycle removal and fixed-size sampling | Proved, with exact counts and explicit constants |
| Theorem 1, VFT setting | Proved in the finite rounded form above |
| Corollary 2, VFT setting | Proved unconditionally in integer-power form, with constant 72 |
| Folklore Moore bound | Proved in a coarse form with uniform constant 2 |
| EFT setting, optimality lower bound, final EFT limitation construction | Not formalized |

See the [statement map](docs/statement-map.md) for the exact correspondence,
parameter conventions, and remaining scope, and the
[verification record](docs/verification.md) for the checks performed.

## New Results on Linear Size Distance Preservers

The implementation lives in the top-level [New Results on Linear Size Distance Preservers](<New Results on Linear Size Distance Preservers/>) folder.

**Theorems 1 and 2 are proved end to end in explicit finite forms.**
`LinearDistancePreservers.theorem_one` constructs an exact distance preserver
with at most `3n + 24p floor(cuberoot(n))²` edges for finite directed graphs
with finite nonnegative weights. `LinearDistancePreservers.theorem_two`
constructs one with at most `2p + 12 M(n)` edges for finite undirected
unweighted graphs, where `M(n)` is the defined maximum edge count of a graph
partitionable into n induced matchings. Neither theorem assumes the required
path selection, routing, lazy trees, cut, or edge-count estimate. The
subquadratic bound on `M(n)` is derived from mathlib's triangle-removal theorem.

The package also proves a concrete counterexample to the Euclidean weighting
displayed in arXiv v4 Theorem 5 and verifies a replacement finite construction.
The original existential theorem is not refuted. **Theorem 3 is now proved
for arbitrary sizes in an explicit finite form; Theorem 4 remains incomplete.**

`TheoremThree.bounded_range_lower_bound` constructs a graph on exactly `N`
vertices and exactly `T` terminals for every `C≥1`, `2≤T≤N`, and
`T³≤C³N²`. Every subset preserver has `T³N²≤(32768C)³E³`.
Its weights are finite, positive, and symmetric. Floors, padding, the small
terminal regime, and arbitrary fixed range constants are proved internally.
The restriction `T≥2` is necessary; one terminal cannot force positive edges.

For Theorem 4, the package now proves vector-graph edge counts and regular
path incidence, the convex-position-to-rigidity bridge, and the actual
unweighted obstacle product's metric and subset-preserver edge count.
The sharp convex-lattice direction-set construction/cardinality and final
parameter selection remain. The paper folder records the precise scope.
Both libraries are built, indexed, and audited.

## An Alternate Proof of Near-Optimal Light Spanners

The initial implementation lives in the top-level [An Alternate Proof of Near-Optimal Light Spanners](<An Alternate Proof of Near-Optimal Light Spanners/>) folder.

**This is a partial formalization.** `LightSpanners.greedy_isSpanner` proves the
walk-stretch guarantee for the implemented weighted greedy algorithm, and
`LightSpanners.greedy_weightedGirth` proves Lemma 3.2 using the last-edge cycle
argument, including equal-weight ties. Additional helpers verify dyadic budgets,
endpoint counting, expectation rearrangement, and stretch reparameterization.

The unit-weight spanning-cycle reduction, bucket-path dispersion, hiker protocol,
sampling argument, and final lightness theorem remain to be formalized.
All 49 initial declarations pass the axiom audit; all three modules compile and
pass separate kernel replay. See the paper folder for exact scope and remaining obligations.

## Unconditional Lower Bounds for Degree Fault Tolerant Spanners

The [paper library](<Unconditional Lower Bounds for Degree Fault Tolerant Spanners/>) proves the repaired new lower-bound result end to end. For every integer `k>=1`, a positive constant `c_k=1/2^(k+3)` is chosen before every `N>=2` and `1<=f<=N`. It constructs an actual N-vertex graph whose every f-degree-fault-tolerant stretch-(2k-1) spanner has at least `c_k*f^(1-1/k)*N^(1+1/k)` edges.

`DegreeFaultSpanners.theorem_five_uniform_parameters` includes nearby-prime selection, isolated padding and dense witnesses internally. The exact prime construction retains constant 1/4. Faults are edge-subgraphs of the input with degree at most f, and the walk formulation is proved equivalent to extended shortest distances. The source incidence-size claim needs k>=2; complete graphs repair k=1, as recorded in the paper's correction log.

All 18 modules and the aggregate compile, all 440 declarations pass the allowed-axiom audit, all 19 modules pass separate official kernel replay, and independent semantic review passes. The paper folder records the precise scope, source hashes and verification evidence. Cited background Theorems 2 and 4 are not claimed formalized.

## Improved Upper Bounds for the Directed Flow-Cut Gap

The [paper library](<Improved Upper Bounds for the Directed Flow-Cut Gap/>) is in progress. Its main n^(1/3+o(1)) and W^(1/2)n^o(1) bounds are not yet formalized. Checked components cover actual directed paths and endpoint-excluding cuts, a repaired positive-weight oracle-to-family sampling reduction, and attained finite packing/covering strong duality.

The paper folder records three independently checked issues in printed proof components, reproducible counterexamples, exact component assumptions and remaining proof obligations. These are not counterexamples to the headline bounds. The partial library participates in the shared build and verification scripts.

## Verification

The repository pins Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; dependencies are locked in
`lake-manifest.json`. GitHub Actions builds the full library on pushes and pull
requests, checks the module index, and audits every project declaration.

The audit rejects proof holes and all axiom dependencies other than
`propext`, `Classical.choice`, and `Quot.sound`. A successful build alone is not
used as evidence that a proof is complete.

For anyone reproducing the verification:

```sh
lake exe cache get
lake build
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

Source: Greg Bodwin and Shyamal Patel, [arXiv:1812.05778v2](https://arxiv.org/abs/1812.05778v2),
1 June 2019. Released under the MIT license; dependencies retain their own licenses.
