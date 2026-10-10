# Bodwin–Patel (2019): statement map

Source: Greg Bodwin and Shyamal Patel, *A Trivial Yet Optimal Solution to Vertex
Fault Tolerant Spanners*, arXiv:1812.05778v2, 1 June 2019.

## Main verified statement

Let `G` be any finite simple undirected graph on `n` vertices. Let its edge
weights be nonnegative real numbers, and let `k ≥ 1` and `f ≥ 1` be integers.
Define `H = greedyOutput G w k f`. Then:

1. `H ≤ G`, and the weight function is unchanged.
2. For every vertex set `F` with `|F| ≤ f` and every pair `u,v`,
   `faultDistance H w F u v ≤ k * faultDistance G w F u v`.
3. `|E(H)| ≤ 36*f²*extremalEdges(max 2 (n/f), k+1)`, with natural-number
   division. `extremalEdges N g` is the maximum actual edge count among **all**
   simple graphs on `Fin N` having no simple cycle of length at most `g`.

This is `vft_greedy_theorem_one` in `PaperTheorem.lean`. Its assumptions contain
only the finite graph, weight nonnegativity, and the displayed parameter
conditions. There is no hypothesis asserting the greedy algorithm's correctness,
a blocking set, a favorable sample, an extremal bound, or the conclusion.

Distances are the infimum of fault-avoiding walk weights in the extended
nonnegative reals; an absent walk gives infinity. At failed endpoints every walk
is excluded. Thus the theorem in particular gives the paper's inequality for
all surviving endpoints. Nonnegative edge weights imply nonnegative walk
weights (`walkWeight_nonneg`), so conversion to extended nonnegative reals does
not truncate the relevant weights.

## Definitions and proof chain

| Source claim | Lean declaration(s) | What is established |
| --- | --- | --- |
| Definitions 1–2, VFT weighted stretch | `IsVFTSpanner`, `faultDistance`, `IsVFTSpanner.distance_le` | Fault-avoiding walk replacements imply the usual distance inequality. |
| Algorithm 1 | `greedyEdges`, `greedyInput`, `greedyOutput` | Recursion accepts an edge exactly when some admissible fault set has no sufficiently short walk. |
| Algorithm 1 distance test | `exists_minimum_walk`, `distance_le_iff_exists_walk`, `covered_iff_distance` | In a finite nonnegative weighted graph, the walk test equals the distance test, including zero-weight edges. |
| Algorithm correctness | `covered_edges_spanner`, `greedy_isVFTSpanner` | Replace each edge of any input walk and concatenate replacements. |
| Definition 3 | `IsBlockingSet` | Every blocking pair uses an original edge and a vertex outside its endpoints; every short simple cycle contains a pair. |
| Lemma 3 | `not_covered_witness`, `extend_blocking`, `greedy_blocking`, `greedyOutput_blocking` | Construct a `(k+1)`-blocking set of at most `f*|E(H)|` pairs from the actual greedy recursion. |
| Lemma 4, girth | `prunedGraph_no_short_cycle` | Sampling vertices and deleting blocked edges removes every short cycle. |
| Lemma 4, exact sampling | `sum_included_card`, `exists_dense_high_girth_sample` | Exact double counting over every fixed-size sample, including the bijection to actual pruned graph edges. |
| Lemma 4, finite constants | `finite_sampling_arithmetic`, `exists_high_girth_sample_finite` | For `n ≥ 6f`, choose `r=floor(n/(2f))`; some pruned `r`-vertex graph has at least `m/(32f²)` edges. |
| Extremal comparison | `extremalEdges`, `edge_count_le_extremal`, `extremalEdges_mono` | The counted graph is bounded by the actual extremal function; padding by isolated vertices proves monotonicity. |
| Theorem 1, VFT | `vft_greedy_theorem_one` | The full construction-to-distance-and-size theorem above, for every `n`, including the dense-fault regime. |
| Zero faults | `vft_greedy_zero_faults` | Ordinary greedy has girth greater than `k+1` and at most `b(n,k+1)` edges. |
| Moore bound, pruning | `exists_dense_core` | More than `d*n` edges imply a nonempty induced subgraph of minimum degree at least `d+1`. |
| Moore bound, path counting | `HighGirth.short_paths_unique`, `rootedPaths_growth`, `moore_min_degree` | In girth greater than `2r`, minimum degree at least `d+1` implies `d^r ≤ n`. |
| Moore bound, extremal form | `moore_edge_bound`, `extremalEdges_moore` | For `r ≥ 1`, every such graph and the exact extremal function satisfy `m^r ≤ 2^r*n^(r+1)`. |
| Corollary 2, modular version | `corollary_two_from_moore` | Retained reusable substitution for any proved Moore constant. |
| Corollary 2, VFT | `mooreBound_two`, `corollary_two_size`, `corollary_two` | Discharge the Moore premise, proving size with constant 72 and the subgraph/distance guarantees together. |

## Algorithm fidelity and tie handling

`greedyInput` sorts the input's unordered edge labels in descending weight order.
`greedyEdges` recurses on the tail first, so the edges are processed in
**nondecreasing** weight order. At each step it either leaves the edge set alone
or inserts exactly the queried edge. No loops or edges outside the input can be
introduced. The fixed enumeration supplies a tie order; the blocking-set proof
`greedy_blocking` applies to any duplicate-free list in the required weight order,
without requiring strictly increasing weights.

The implementation is a noncomputable mathematical specification using the
exact classical existence test. It is not a claimed efficient executable
implementation. `Runtime.lean` checks the combinatorial cost of naive exhaustive
fault enumeration; it does not attach machine costs to the specification.

The fault set in the test excludes the two endpoints. This is implicit in
querying their distance after vertex deletion and is explicit in `Covered`.
`not_covered_witness` shows that the resulting witness works for either
orientation of the undirected edge. The new blocking pairs exclude both
endpoints, as required by Definition 3.

## Exact sampling and rounding

The earlier exact counting theorem remains unchanged: for `3 ≤ r ≤ n`,
there is a sample with `r` vertices and `q` retained edges such that

`m*choose(n-2,r-2) ≤ choose(n,r)*q + |B|*choose(n-3,r-3)`.

The proof now derives the two binomial-ratio identities, uses `|B| ≤ f*m`, and
specializes to `r=floor(n/(2f))` when `n ≥ 6f`. This deliberately uses a floor
instead of the paper's ceiling; it proves a valid finite version with constant
32, avoiding `o(1)` estimates. The graph in the counting argument is exactly the
graph in the girth argument.

For `n < 6f`, the trivial simple-graph edge bound and `b(2,g) ≥ 1` give the final
constant 36. The intermediate bound is actually
`m ≤ 36*f²*b(max(2,floor(n/(2f))),k+1)`; isolated-vertex padding yields the
reported `n/f` version. The `max 2` convention is essential to give a literal
integer statement when `f` is comparable to, or exceeds, `n`. For `n ≥ 2f` it is
just `b(floor(n/f),k+1)`.

## Corollary 2: unconditional finite statement

For positive integers `r,f`, `corollary_two` proves that the actual
stretch-`2r-1` weighted greedy output `H` is a subgraph of `G`, satisfies the
fault-distance guarantee above, and has edge count `m` satisfying

`m^r ≤ 72^r*n^(r+1)*f^(r-1)`.

Its only hypotheses are a finite simple input graph, nonnegative real edge
weights, `r ≥ 1`, and `f ≥ 1`. There is no extremal-bound hypothesis.
The result includes empty input graphs, `r=1`, and the dense-fault case.
The checked `real_bound_of_power_bound` takes the `r`th root, giving
`m ≤ 72*n^(1+1/r)*f^(1-1/r)` over the reals, with constant 72 uniform in all
parameters. `vft_corollary_two_real` and `eft_corollary_two_real` instantiate it.
This explicit pointwise estimate is stronger than the paper's Big-O notation.

The earlier `corollary_two_from_moore` remains as a useful modular lemma. It
accepts `MooreBound r C`, defined as
`∀ N, b(N,2r)^r ≤ C^r*N^(r+1)`, and proves the same result with `36*C`.
`mooreBound_two` now supplies that premise as a proved theorem with `C=2`.

### Proof of the needed Moore bound

The self-contained module `Moore.lean` uses the existing mathlib dependency.
It proves a coarse uniform bound, without claiming the sharp irregular-graph
Moore bound or depending on another project's formalization.

1. Among vertex sets inducing more than `d*|U|` edges, choose one of minimum
   cardinality. Removing a vertex of degree at most `d` would preserve that
   strict inequality, a contradiction. Thus its minimum degree is at least
   `d+1` and it is nonempty.
2. Two distinct simple paths with the same endpoints and total length at most
   `2r` would contain a forbidden cycle. Every rooted simple path of length
   less than `r` therefore has at least `d` extensions when its preceding
   vertex is excluded. Different paths of length `r` have different endpoints,
   proving `d^r ≤ |U| ≤ n`.
3. For `m>n>0`, use `d=floor((m-1)/n)`. Then `d≥1`, `d*n<m`, and
   `m≤(d+1)*n≤2*d*n`, which yields `m^r≤2^r*n^(r+1)`.
   Empty graphs and `m≤n` are handled separately.
4. Apply this inequality to a graph attaining the finite maximum defining
   `extremalEdges n (2*r)`, and substitute the result into the existing
   corollary lemma.

## EFT extension

`EdgeFault.lean`, `EdgeGreedy.lean`, `EdgeMain.lean`, and
`EdgeShortestPaths.lean` formalize the actual edge-fault version of Algorithm 1.
Fault avoidance quantifies over the **edges** of a walk. The fault distance is
an infimum over such walks, with infinity when none exists.

- `edgeGreedyEdges` performs the exact classical edge-fault test.
- `edgeCovered_iff_distance` proves equivalence with the shortest-distance test.
- `edgeCovered_iff_all_faults_of_absent` verifies the paper's pseudocode even
  when a candidate fault set contains the queried edge: before insertion that
  edge is absent, so removing it from the fault set leaves the test unchanged.
- `greedy_isEFTSpanner` constructs fault-avoiding replacements for every walk.
- `covered_implies_edgeCovered` selects one endpoint of each failed edge outside
  the queried edge. This reduces the size analysis to the proved VFT blocking
  argument without changing the EFT algorithm.
- `edgeGreedyOutput_blocking` constructs a vertex blocking set of at most
  `f*|E(H)|` pairs for the EFT output.
- `eft_greedy_theorem_one` proves the same subgraph, weighted distance, and
  `36*f²*b(max(2,floor(n/f)),k+1)` bounds as the VFT theorem.
- `eft_corollary_two` discharges the Moore bound and proves the same uniform
  constant 72 as the VFT corollary.
- `EdgeBlocking.lean` separately proves the final paragraph's edge-pair analog
  of Lemma 3 for the actual EFT output.

## Final edge-blocking limitation construction

`EdgeLimitation.lean` defines `independentBlowup G t` on `V × Fin t`:
vertices are adjacent exactly when their first coordinates are adjacent in `G`.
This replaces each base edge by a complete bipartite graph between its fibers.
The paper calls it a Cartesian product; the implemented operation is the
independent blowup intended by the paper's description and edge count.

- A dart equivalence proves exactly `t²*|E(G)|` blowup edges.
- The explicit blocker set pairs distinct incident blowup edges projecting
  onto the same base edge. Its **ordered** cardinality is at most
  `2*(t-1)*|E(H)|`; the unordered count is therefore no larger.
- A short projected walk with no repeated consecutive edges is a path in a
  high-girth graph. Projecting a short blowup cycle contradicts this unless it
  contains one of the declared blocking pairs.
- `edge_blocking_limitation n t k` takes an actual extremal graph and constructs
  `H` with exactly `n*t` vertices, `t²*b(n,k)` edges, and those blockers.
- `edge_blocking_limitation_faults n f k hf` uses `t=floor(f/2)` for `f≥2`.
  Writing `N=n*t`, it proves `|B|≤f*|E(H)|` and
  `f²*b(floor(N/f),k)≤9*|E(H)|`. The `f=1` case is proved separately.

This is a limitation of the blocking-set property. It does **not** claim these
blowups are EFT-greedy outputs or prove an EFT-spanner lower bound.

## Runtime observation

`Runtime.lean` defines the finite schedule for an eager exhaustive
implementation: all candidate edges crossed with all fault subsets of the
allowed universe of size at most `f`. The checked cardinality is
`m*sum_{j=0}^N (if j≤f then choose(N,j) else 0)`.
If `f≤N`, it has at least `m*2^f` queries, and it never has more than `m*2^N`.
The fault universe is surviving vertices for a VFT edge test, or eligible
input edges for an EFT test. The distance-test equivalence theorems justify
using these fault sets in Algorithm 1.

This verifies the paper's informal observation about naive enumeration. It
is not a worst-case lower bound for all implementations, does not assert that
short-circuit evaluation visits every fault set, and does not analyze a
particular shortest-path implementation, memory model, or bit complexity.

## Scope classification

The original proved mathematical claims are Algorithm 1 correctness,
Theorem 1 (VFT and EFT), Corollary 2 (VFT and EFT), Lemmas 3 and 4, the
edge-blocking analog of Lemma 3, and the final edge-blocking limitation family.
They are covered by the declarations above in exact finite forms. The informal
runtime observation has the explicit exhaustive-enumeration interpretation above.

The VFT optimality lower bound and EFT lower bounds for small stretch are
explicitly imported from Bodwin–Dinitz–Parter–Williams (2018), reference [9].
They are external background, not new results in this paper and not premises
in the formalized upper bounds. The Moore bound was folklore background, but
a sufficient version is additionally proved here. Prior-work comparisons,
historical open questions, and the Erdős girth conjecture are not claimed as
new formal theorems. No external result is silently turned into an axiom.
