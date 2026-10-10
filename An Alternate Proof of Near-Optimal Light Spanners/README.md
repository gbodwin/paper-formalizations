# An Alternate Proof of Near-Optimal Light Spanners

Lean formalization in progress of Greg Bodwin's paper, TheoretiCS 4 (2025), Article 2.
Source: https://arxiv.org/abs/2305.18647v6
DOI: https://doi.org/10.46298/theoretics.25.2

**Partial: Theorem 5.1 and the final lightness guarantee remain unproved.**
No `sorry` proofs, project axioms, or assumed substitutes for missing paper lemmas
are introduced.

## Current milestone

`greedyOutput_preliminaries` establishes, for any finite connected simple graph,
nonnegative real weights, and real stretch `t >= 1`:

- the implemented greedy output is a subgraph with walk and shortest-distance stretch;
- its weighted girth is greater than `t+1`;
- it contains a minimum-total-weight spanning tree of the original graph.

The implementation sorts the actual input edges. MST minimality is proved by
a complete edge-exchange argument, including equal-weight ties. Sorting and an
assumed MST are not premises of the combined theorem.

## Continuation milestone — 2026-10-10

The one-edge subdivision is now an explicit graph on `Option V`. Original
walks lift with the same weight, subdivided walks contract without increasing
weight, and weighted distances between original vertices are equal. This
includes disconnected pairs and zero replacement weights. Connectedness and
positive edge weights are also preserved under their stated hypotheses.

Every simple cycle in the subdivided graph contracts to an actual original
simple cycle with precisely the same total weight, whether or not it visits
the inserted vertex. A separate bottleneck-tree theorem selects a heaviest
cycle edge outside the tree, including equal-weight ties.

The new `WeightedGirthAbove.subdivideEdge` theorem proves that subdividing
any edge into two nonnegative pieces of the same total weight cannot decrease
a nonnegative weighted-girth lower bound. This is an actual graph theorem,
using the simple-cycle contraction; it is not merely an arithmetic implication.

The new one-edge tree bridge preserves acyclicity and spanning-tree inclusion.
It lifts bottleneck-bounded walks, proves the subdivided tree is an MST, and
proves exact preservation of total graph weight, total tree weight, and lightness.

The rounding step now has a graph-level MST and factor-two lightness proof
using the global vertex budget. It handles pre-existing arbitrarily light
tree edges and does not assume the paper's pointwise lower bound of one-half.
See `verification/SOURCE-CORRECTIONS.md` for the counterexample and repair.

The actual unit-MST stage of Lemma 3.5 is now constructed by
`unit_tree_reduction_of_mst`: Kruskal supplies the needed bottleneck paths,
positive scaling normalizes tree weight, well-founded repeated subdivision
creates an actual graph with at most `2n−1` vertices, and global rounding
produces a unit-weight MST. The output remains non-forest, preserves the
weighted-girth lower bound, and has at least half the original lightness.
No post-subdivision graph or cardinality bound is assumed by this theorem.

The complete Lemma 3.5 reduction is now constructed by
`unit_spanning_cycle_reduction_of_mst`. From a positive-weight non-forest graph,
a nonnegative girth threshold, and any explicit reference MST, it constructs
an actual graph on `Fin n′` with `n′ ≤ 4n−4`, a unit spanning cycle, an actual
MST, the same weighted-girth lower bound, and at least one quarter of the
original lightness. The spanning tree tour, vertex copies, chord projection,
and total-weight comparison are proved internally.

All 35 modules compile; all 564 declarations pass the permitted-axiom audit.
All 35 modules pass independent kernel replay, and independent semantic review
of the copy/girth, final composition, Claim 2 and dispersion arguments passes. See
`verification/CYCLE-REDUCTION-VERIFICATION-2026-10-10.md`. This remains a partial
paper formalization: bucket-path arguments, sampling, and final lightness remain
open. Exact normalized-girth equality is not claimed; lower-bound preservation
suffices for the reduction.

The actual safe, extra-safe, and bucket-monotone walk predicates in Definitions
5.2 and 5.4 are now formalized, including empty blocks and permitted backtracking
between blocks. Claim 3 is proved: `BucketMonotoneKPath.chordEdges_nodup` gives
exactly `k` distinct non-cycle edges under `ε>0`, `k≥1`, and weighted girth
above `(1+4ε)2k`. A stronger intermediate theorem proves each nonempty-in-chords
bucket block is a simple path when it has at most `k` chords. The full
concatenation is not required to be non-backtracking or globally simple.
Claim 2 is now proved for actual oriented chord words and a common terminal
vertex: `BucketSafe.unique_of_chordDarts` identifies the entire walk even when
the start vertices and bucket indices differ. It assumes no simplicity or
chord-count bound. Cyclic displacement balance determines the initial vertex;
short non-backtracking base arcs determine all gaps between the oriented chords.
The empty-chord case is proved to be the empty walk. See
`verification/BUCKET-CLAIM-TWO-VERIFICATION-2026-10-10.md`.
Dispersion Lemma 5.5 is now proved for the actual walk predicates:
`BucketMonotoneKPath.unique` says two such k-walks with the same endpoints are
equal, in ordinary or extra-safe mode. Generic bridge-word uniqueness derives
an actual cycle containing a differing top-bucket chord inside the two walks'
support. The actual cycle's chord and base-step counts contradict weighted girth.
Padding by empty blocks handles different decomposition lengths. No global
simplicity, supplied cycle, or shared-decomposition premise is assumed.
Hiker construction, counting, sampling and final lightness remain open.

## Paper correspondence

| Ingredient | Declaration | Scope |
|---|---|---|
| Definition 1.1 | `isSpanner_iff_distance` | Exact equivalence of walk and shortest-distance stretch for finite nonnegative-weight graphs and positive stretch, including disconnected pairs. |
| Algorithm 1 test | `covered_iff_distance` | Exact shortest-distance interpretation, with minimum walks proved by loop erasure and finite minimization, including zero weights. |
| Algorithm 1 | `greedyInput`, `greedyOutput`, `greedyOutput_preliminaries` | Actual edge enumeration and sorting, stretch, girth, and MST containment. |
| Definition 3.1 | `weightedGirthAbove_iff_normalized` | Actual cycle sum divided by its maximum edge weight, for positive graph weights and nonnegative threshold. |
| Lemma 3.2 | `greedy_weightedGirth` | Last-edge cycle argument with equal-weight ties. |
| MST containment | `kruskal_subset_greedy`, `kruskal_isMinimumSpanningTree`, `greedy_contains_mst` | Constructed spanning forest, bottleneck paths, and total-weight minimum via exchanges. |
| Section 3.2 scaling | `weightedGirthAbove_scale_iff`, `isSpanner_scale_iff`, `lightness_scale`, `IsMinimumSpanningTree.scale` | Positive scaling preserves graph-level girth, stretch, lightness, and MST optimality. |
| Section 3.2 rounding | `WeightedGirthAbove.round_up`, `totalWeight_round_up_le_double` | Rounding to at least one preserves weighted girth; weight grows by at most two when all original edge weights are at least one-half. |
| Lemma 3.5 subdivision estimates | `subdivision_piece_bounds`, `subdivision_weight_preserved`, `subdivision_vertex_budget`, `subdivision_normalized_vertex_count` | Equal pieces have weight in (1/2,1], preserve total weight, and give at most 2n-1 vertices after normalization. The actual iterated construction and its vertex budget are now proved in `TreeReduction.lean`. |
| One-edge subdivision | `subdivideEdge`, `exists_subdivision_lift`, `exists_subdivision_contraction`, `subdivision_distance_eq` | Actual graph construction, walk-weight preservation, and exact weighted distances on original vertices. |
| Simple-cycle contraction | `subdivision_cycle_contract` | Every subdivision cycle contracts to an original simple cycle of identical weight. |
| One-edge weighted-girth transfer | `WeightedGirthAbove.subdivideEdge` | Splitting an edge into nonnegative pieces preserves every nonnegative weighted-girth lower bound. This proves nondecrease, not equality of normalized girth. |
| Lemma 3.5, unit-MST stage | `unit_tree_reduction_of_mst` | Constructs the finite reduced graph from any explicit reference MST, with at most 2n−1 vertices, unit MST, non-forest output, preserved girth threshold, and at least half lightness. Includes scaling, repeated subdivision, and rounding. |
| Lemma 3.5, complete reduction | `unit_spanning_cycle_reduction_of_mst` | Constructs an actual unit spanning cycle and MST, at most 4n−4 vertices, preserved girth threshold, and at least quarter lightness. No tour, copied graph, cycle correspondence, or vertex budget is assumed. |
| Spanning-tree tour and vertex copies | `exists_tree_tour`, `exists_tree_vertex_copies`, `unit_tree_to_spanning_cycle` | A closed spanning tree walk of length 2(n−1) produces the actual position cycle and representative copies. |
| Girth under vertex copying | `WeightedGirthAbove.cycle_projection_bound`, `VertexCopies.weightedGirthAbove` | Projects a cycle complement and erases loops while preserving a selected uniquely lifted chord; base-only cycles are treated separately. No cycle-set bijection is assumed. |
| Copy weights and MST | `VertexCopies.totalWeight_graph`, `VertexCopies.exists_mst_lightness` | Exact base-plus-chords weight decomposition, nondecreasing graph weight, actual MST, and factor-two lightness transfer. |
| Global rounding repair | `tree_round_up_weight`, `round_up_isMinimumSpanningTree`, `normalized_round_up_lightness` | Unit MST and factor-two lightness transfer from an actual vertex-budget hypothesis, without a lower bound on old tree edges. |
| One-edge tree/MST/lightness transfer | `subdivideEdge_isTree`, `HasBottleneckPaths.subdivideEdge`, `subdivision_isMinimumSpanningTree`, `totalWeight_subdivideEdge`, `lightness_subdivideEdge` | Actual tree, bottleneck-path, MST minimality, and exact finite-sum/lightness preservation for one selected tree edge. |
| Tree-cycle maximum | `exists_nontree_cycle_max` | A heaviest cycle edge can be chosen outside a bottleneck spanning tree, including ties. |
| Unit spanning cycle | `UnitSpanningCycle`, `UnitSpanningCycle.exists_short_path` | Actual oriented Hamiltonian cycle and constructed paths of weight at most n/2. |
| Lemma 3.7, chord form | `UnitSpanningCycle.chord_weight_lt` | Non-cycle edges weigh less than n/(2(g-1)) for weighted girth above g > 1. |
| Unit-cycle MST weight | `UnitSpanningCycle.mst_weight`, `UnitSpanningCycle.lightness_eq` | MST weight is exactly n-1, giving the exact lightness denominator. |
| Definitions 5.2 and 5.4 | `BucketWalk`, `BucketSafe`, `BucketExtraSafe`, `BucketMonotoneWalk`, `BucketMonotoneKPath` | Actual graph walks, actual oriented cycle darts, equal forward/backward counts, dyadic chord weights, empty blocks and blockwise non-backtracking. |
| Claim 2 | `BucketSafe.unique_of_chordDarts` | Equal oriented chord words and a common terminal vertex imply heterogeneous equality of the actual bucket-safe walks. Different starts and bucket indices are allowed; no simplicity or chord-count bound is assumed. |
| Lemma 5.5 | `BucketMonotoneKPath.unique` | Actual endpoint uniqueness, including support-local marked-cycle extraction, derived cycle/chord budgets and differing decomposition lengths. Ordinary and extra-safe modes are both covered. |
| Claim 3 | `BucketMonotoneKPath.chordEdges_nodup` | No repeated non-cycle edge in a bucket-monotone k-walk. Proved from positive ε, k≥1, the unit-cycle certificate, and the actual weighted-girth threshold; no simplicity or dispersion premise. |
| Counting arithmetic | `bucket_budget`, `dispersion_arithmetic`, `endpoint_count`, `sampling_bootstrap`, `counting_sandwich` | Helpers only; their combinatorial inputs remain open. |

Weights are on unordered pairs `Sym2 V`. Graph walks, paths, cycles, Hamiltonian
cycles, and trees use mathlib `SimpleGraph`. `IsMinimumSpanningTree` minimizes
the actual finite sum over all spanning trees. `lightness G T w` uses an explicit
reference MST; `lightness_mst_independent` proves independence among tied MSTs.
The list algorithms process tails first, and `greedyInput` supplies descending
weight order. Separate distance/stretch results cover disconnected graphs.

The strict Lemma 3.7 bound is used for non-cycle edges. Unit cycle edges require
a separate case: `edge_weight_le_max` gives the uniform bound
`max 1 (n/(2(g-1)))`. A bare n-cycle shows why the strict chord bound cannot be
applied indiscriminately to unit cycle edges.

## Remaining work in paper order

1. Formalize Lemma 5.8's hiker protocol: suffix swaps, occupancy, cancellation,
   and integer rounding. Handle small buckets explicitly; the displayed floor
   estimate requires an appropriate lower bound on its argument.
2. Prove Lemma 5.10's truncation/extension/deletion argument. Claim 3's
   distinctness of non-cycle edges is now proved.
3. Construct independent edge sampling, survival probabilities, expectation
   bounds, and Lemma 5.13.
4. Assemble Theorem 5.1 with explicit constants and transfer through the reductions.

There is no declaration claiming the complete lightness theorem.

## Verification and recovery

The continuation compiles with Lean 4.34.0. All 564 declarations pass the
permitted-axiom audit and all 35 modules pass independent kernel replay.
See `verification/DISPERSION-VERIFICATION-2026-10-10.md` for the precise
scope and check record. The preceding Claim 3 checkpoint (27 modules, 435
declarations) passed full repository-wide CI at
[commit 0e29d002](https://github.com/gbodwin/paper-formalizations/actions/runs/38062078307).
The preceding complete graph-reduction checkpoint
(25 modules, 381 declarations) passed full repository-wide CI at
[commit 68bb4189](https://github.com/gbodwin/paper-formalizations/actions/runs/38060761128).
`verification/CYCLE-REDUCTION-VERIFICATION-2026-10-10.md` records that milestone. The preceding 19-module, 282-declaration
unit-MST checkpoint passed full repository-wide CI at
[commit e742a8b0](https://github.com/gbodwin/paper-formalizations/actions/runs/38057329186).
`verification/UNIT-TREE-VERIFICATION-2026-10-10.md` records that checkpoint.
`verification/ROUNDING-VERIFICATION-2026-10-10.md` records the preceding
252-declaration checkpoint, which passed full repository-wide CI at
[commit 4a9fed24](https://github.com/gbodwin/paper-formalizations/actions/runs/38055817568).
`verification/TREE-VERIFICATION-2026-10-10.md` records the preceding
247-declaration tree-transfer checkpoint.
`verification/GIRTH-VERIFICATION-2026-10-10.md` records the preceding
221-declaration checkpoint, which passed full repository-wide CI at
[commit 1e6c5775](https://github.com/gbodwin/paper-formalizations/actions/runs/38053664074).
`verification/CONTINUATION-2026-10-10.md` records the preceding 213-declaration checkpoint.
`verification/MILESTONE-VERIFICATION.md` records the historical 181-declaration
checkpoint. Repository-wide checks are delegated to the branch CI; no
repository-wide completion is claimed by the targeted checks above.

Run from the repository root with its unchanged Lean 4.34.0 and mathlib pin:

```sh
lake exe cache get
lake build LightSpanners
lake env lean "An Alternate Proof of Near-Optimal Light Spanners/verification/AllDeclarationsAudit.lean"
lake env lean "An Alternate Proof of Near-Optimal Light Spanners/verification/SelectedAxioms.lean"
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The all-declarations audit includes private/generated declarations and permits
only `propext`, `Classical.choice`, and `Quot.sound`. Existing `.txt` logs record
the initial package; the milestone verification record distinguishes later runs.

Graph-walk conventions and edge sorting follow the existing VFTSpanners package;
this package does not import that paper's modules. Code uses the repository MIT
license; the mathematical paper is CC BY 4.0. Existing root build, index, axiom,
and kernel checks already include LightSpanners.
