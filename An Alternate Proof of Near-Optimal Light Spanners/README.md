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

All 15 modules compile; all 213 declarations pass the permitted-axiom audit;
all 15 modules pass independent kernel replay. This remains a partial paper
formalization. In particular, inverse cycle lifting, weighted-girth transfer
through repeated subdivision, and the final lightness theorem remain open.

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
| Lemma 3.5 subdivision estimates | `subdivision_piece_bounds`, `subdivision_weight_preserved`, `subdivision_vertex_budget`, `subdivision_normalized_vertex_count` | Equal pieces have weight in (1/2,1], preserve total weight, and give at most 2n-1 vertices after normalization. The one-edge graph and cycle contraction are now proved; iterated subdivision remains open. |
| One-edge subdivision | `subdivideEdge`, `exists_subdivision_lift`, `exists_subdivision_contraction`, `subdivision_distance_eq` | Actual graph construction, walk-weight preservation, and exact weighted distances on original vertices. |
| Simple-cycle contraction | `subdivision_cycle_contract` | Every subdivision cycle contracts to an original simple cycle of identical weight; this is not yet the complete weighted-girth transfer. |
| Tree-cycle maximum | `exists_nontree_cycle_max` | A heaviest cycle edge can be chosen outside a bottleneck spanning tree, including ties. |
| Unit spanning cycle | `UnitSpanningCycle`, `UnitSpanningCycle.exists_short_path` | Actual oriented Hamiltonian cycle and constructed paths of weight at most n/2. |
| Lemma 3.7, chord form | `UnitSpanningCycle.chord_weight_lt` | Non-cycle edges weigh less than n/(2(g-1)) for weighted girth above g > 1. |
| Unit-cycle MST weight | `UnitSpanningCycle.mst_weight`, `UnitSpanningCycle.lightness_eq` | MST weight is exactly n-1, giving the exact lightness denominator. |
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

1. Complete Lemma 3.5: iterated heavy-MST-edge subdivision, inverse cycle lifting and weighted-girth transfer, and the
   Euler-tour vertex-copy construction of a unit spanning cycle, preserving
   girth and lightness. Scaling, rounding, MST ingredients, and numerical subdivision bounds are now available.
2. Define safe and extra-safe bucket walks and bucket-monotone concatenation,
   allowing empty blocks and imposing non-backtracking within each bucket.
3. Prove Claim 2, last-differing-bucket cycle extraction, and dispersion Lemma 5.5.
4. Formalize Lemma 5.8's hiker protocol: suffix swaps, occupancy, cancellation,
   and integer rounding. Handle small buckets explicitly; the displayed floor
   estimate requires an appropriate lower bound on its argument.
5. Prove Lemma 5.10's truncation/extension/deletion argument and Claim 3's
   distinctness of non-cycle edges.
6. Construct independent edge sampling, survival probabilities, expectation
   bounds, and Lemma 5.13.
7. Assemble Theorem 5.1 with explicit constants and transfer through the reductions.

There is no declaration claiming the complete lightness theorem.

## Verification and recovery

The continuation compiles with Lean 4.34.0. All 213 declarations pass the
permitted-axiom audit, all 15 modules pass independent kernel replay, and the
source import index matches all 15 modules. See
`verification/CONTINUATION-2026-10-10.md` for the precise scope and checks.
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
