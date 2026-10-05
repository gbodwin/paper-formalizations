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
implementation. The paper's exponential-runtime discussion is not formalized.

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
Taking the `r`th root gives the paper's `O(n^(1+1/r)*f^(1-1/r))` form, with
constant 72 uniform in the parameters. The integer-power inequality is checked
in Lean; the real-exponent/Big-O restatement is not separately formalized.

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

## Remaining scope

This is an end-to-end formalization of the main **VFT** construction and size
argument, not a complete formalization of all statements in the paper.
The following remain unformalized:

- The EFT version of Algorithm 1 and Theorem 1.
- A formal real-exponent/Big-O restatement of the proved integer-power bound.
- The VFT optimality lower bound imported from Bodwin–Dinitz–Parter–Williams
  (2018), and the paper's final edge-blocking-set limitation construction.
- Runtime claims and historical/comparative statements.

All existing proof declarations are complete. Remaining work is recorded here,
not represented by admitted theorems or extra axioms.
