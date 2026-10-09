# Unconditional Lower Bounds for Degree Fault Tolerant Spanners

Greg Bodwin and Aleksey Lopez · ESA 2026 · [arXiv:2607.07576v1](https://arxiv.org/abs/2607.07576v1)

**The repaired lower-bound result is formalized and locally verified end to end.**

All 18 implementation modules and the aggregate import module pass the complete
build, exact module index, declaration-wide axiom audit, separate official kernel
replay, and independent semantic review. This includes every N>=2, 1<=f<=N and
k>=1, the exact incidence/cloud family, and the separate k=1 repair. All 440
project declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Remote publication and CI are tracked separately from these local results.

Pinned source: the 8 July 2026 arXiv v1 PDF, SHA-256
`cbf9a322032cd3c672b663ef8547e74a76435ce6df81ab0c3ad77e70d66f8699`.
See [CORRECTIONS.md](CORRECTIONS.md) for the preserved source correction and
proof-convention record. The original PDF is unchanged.

## Mathematical contracts in the source

All declarations below are in namespace `DegreeFaultSpanners`.

### Exact construction and arbitrarily large family

For integers `k >= 2`, prime `p`, and `f >= 1`, `paperGraph` over `ZMod p`
is the actual cloud blowup of the finite-field point/subset-line incidence
graph. `paperGraph_counts` and `paperGraph_spanner_eq` state:

- `N = 2*f*p^k` vertices and `M = f^2*p^(k+1)` edges
- Every `f`-degree-fault-tolerant stretch-`2*k-1` spanner `H` equals that graph
- `family_scaling` gives `2^(k+1)*M^k = f^(k-1)*N^(k+1)`

The implementation uses dimension `d+2` and sets `d=k-2`. Its indexed line
type is justified by `lineSet_injective` and `range_lineSet`: it represents
exactly the paper's distinct affine subset-lines in the corrected domain,
not extra slope-labelled copies. The construction lemmas work over any finite
field; the paper's prime fields are instantiated in the final family theorem.
No girth conjecture or assumed extremal graph is an input to that theorem.

`theorem_five` and `theorem_five_real` quantify over every `k >= 1`, `f >= 1`,
and target threshold `N₀`. They construct a finite simple unweighted graph
with `N >= max(N₀,2)` such that every qualifying spanner satisfies

`|E(H)| >= (1/4) * f^(1-1/k) * N^(1+1/k)`.

The exponents here are real exponents. `real_lower_bound_of_power` supplies
the bridge from the explicit natural-number power inequality. Infinitely many
primes supply the unbounded family for `k>=2`; this family theorem does not
prescribe an independently chosen exact `N`.

For `k=1`, the source instead uses the complete graph. `one_spanner_eq`,
`exists_complete_one_lower_bound`, and `complete_graph_quadratic_lower_bound`
give exactly `N choose 2` compulsory edges and `N^2 <= 4*(N choose 2)` for
`N>=2`. This stretch-one argument works for every natural fault budget,
including budgets greater than `N`.

### Every admissible size and fault budget

The additional declarations `theorem_five_all_sizes` and
`theorem_five_uniform_parameters` give the explicit all-size contract:

For every integer `k >= 1`, set `c_k = 1/2^(k+3) > 0`. For every pair of
integers `N >= 2` and `1 <= f <= N`, there is a finite simple unweighted graph
with **exactly `N` vertices** such that every `f`-degree-fault-tolerant
stretch-`2*k-1` spanner satisfies

`|E(H)| >= c_k * f^(1-1/k) * N^(1+1/k)`.

The constant depends only on `k`, not on `N` or `f`.
`theorem_five_all_sizes_power` first establishes
`f^(k-1)*N^(k+1) <= (2^(k+3))^k * |E(H)|^k`;
`real_lower_bound_of_power_factor` then supplies the real-exponent form.

This is an explicit interpolation extension beyond the paper's written
prime-parameter argument, not a verbatim statement of its implicit quantifiers:

- For `k>=2` and `2^(k+1)*f <= N`, Bertrand's postulate and an integer root
  select a prime family size `N'` with `N' <= N <= 2^k*N'`. Embedding into
  `Fin N` adds isolated vertices, preserves the edge count, and preserves
  edge forcing.
- In the remaining regime, `exists_dense_all_N` uses full cliques of size
  `f+1` with an isolated remainder, or `K_N` when `f=N`. It gives maximum
  degree at most `f`, at least `N*f/4` edges, and rigidity for every natural
  stretch. These are actual constructed graphs, not assumed density data.
- `k=1` uses the complete-graph repair. The uniform all-size constant is
  `1/16` in this case; the separate complete-graph/family statement retains
  the stronger constant `1/4`.

No unrestricted unsaturated lower bound for independently chosen `f>N` is
asserted when `k>1`. The all-size witnesses need not be bipartite; the direct
incidence/cloud family is bipartite.

## Metric and fault semantics

Definitions 1 and 3 are implemented in their **finite simple unweighted,
positive integral-stretch specialization**. The paper's general weighted
spanner definition is not claimed to have been formalized in full. Unit-weight
witnesses suffice for the lower bound.

`IsDegreeFaultSpanner G H f t` requires `H <= G` on the same vertex type and
replacement walks after every admissible edge-fault graph `F`. Admissibility
means `F <= G` and at most `f` incident faulty edges at every vertex. Faults
need not be contained in `H`; vertices are never removed.

For `t>0`, `isDegreeFaultSpanner_iff_edist` identifies this exactly with
`edist_(H-F)(u,v) <= t * edist_(G-F)(u,v)` for all vertices and admissible
faults. Distances lie in `Nat` extended by infinity (`ℕ∞`), so disconnected
pairs are represented by infinity. The lower-bound stretch `2*k-1` is
positive for every admitted `k`. `hasDegreeBound_iff_degree` ties the fault
bound to ordinary graph degree. `isDegreeFaultSpanner_self` also shows that
the positive-stretch spanner condition has a witness.

## Source correction and proof conventions

The subset-line construction in Section 2.1 and Lemma 6 requires `k>=2`.
At `k=1`, every slope is `(1)` and every defined subset-line is the whole
field. The displayed graph is `K_(p,1)`, with `p+1` vertices and `p` edges,
not the stated `2p` and `p^2`. Lemma 16 inherits this count error. The separate
complete-graph argument repairs Theorem 5. The independent source audit
confirmed the issue; it was reported to Greg on 8 October 2026. This source
mathematics audit and the final independent Lean semantic audit both passed for the corrected result.
The website edition will explain the repair and retain a clear changelog
without modifying the original paper PDF.

The formal development also makes explicit:

- Lemma 9 is point-rooted, with distinct point endpoints across each line
  occurrence. Repeated slopes are counted with multiplicity and grouped
  before applying independence. Simple-cycle applications satisfy this
  convention, avoiding the source's line-rooted closing-seam ambiguity.
- Definition 8 uses `2*(r+1) <= k` for line-length `r`, equivalently
  `path.length+2 <= k`; odd dimensions and zero-length paths retain the
  intended cutoff.
- Lemma 10 is endpoint uniqueness, not existence of a reachable endpoint.
  If none is reachable, any point of the nonempty target line suffices.
- Lemma 11 bounds the matching after adjoining the protected edge.
- Path straightening constructs a walk, then erases loops without adding
  slopes. In the lifted proof, `survivingProjection` avoids the entire base
  matching, including the protected base edge; loop erasure justifies the
  simple-cycle argument even for a projected walk with repetitions.

## Numbered statement map

Every in-scope row below has passed compilation, axiom/kernel checks, and independent semantic review under its stated representation and parameter conventions.
The map covers all 17 numbered items used in the paper's new argument;
Theorems 2 and 4 are separately excluded background results.

| Source | Source declarations and scope |
|---|---|
| Definition 1 | `DistanceStretch`, `WalkStretch`, `walkStretch_iff_distanceStretch`; unit-weight specialization |
| Definition 3 | `AdmissibleFault`, `HasDegreeBound`, `IsDegreeFaultSpanner`, `isDegreeFaultSpanner_iff_edist` |
| Theorem 5 | `theorem_five`, `theorem_five_real`; all-size extension: `theorem_five_all_sizes`, `theorem_five_uniform_parameters` |
| Section 2.1; Lemma 6 | `affineLine`, `lineSet`, `range_lineSet`, `lineSet_injective`, `incidenceGraph`, `lemma6_size`; corrected `k>=2` |
| Definition 7 | `Parallel`, `transverseGraph`, `IncidenceWalkEncoding`; simple paths use `Walk.IsPath`, line-length is half the edge length |
| Definition 8 | `shortFailure`, `failureGraph`, `shortFailure_iff_transverse_path`, `shortReach_iff_exists_transverse_path_halfLength` |
| Lemma 9 | `coefficients_eq_zero_of_moments_fintype`, `no_singleton_slope`, `closed_incidence_walk_no_singleton_slope`, `IncidenceWalkEncoding.no_singleton_slope_of_nonbacktracking`, `incidence_cycle_exists_parallel` |
| Lemma 10 | `ShortReach.endpoint_unique_on_line`, `exists_shortReach_endpoint`, together with `shortReach_iff_exists_transverse_path`; parallel lines have the same slope |
| Lemma 11 | `matchingGraph_degree_bound`, `failureGraph_admissible`; protected edge included in the matching |
| Lemma 12 | `incidence_walk_straightening`, `restricted_walk_straightening`, `transverse_walk_straightening` |
| Lemma 13 | `compressed_cycle_shortFailure` in encoded, oriented-cycle form; `matchingGraph_long` assembles the actual graph-walk obstruction |
| Theorem 14 | `incidence_spanner_eq`; corrected incidence domain `k=d+2>=2`, with stretch-one rigidity separately supplied by `one_spanner_eq` |
| Definition 15 | `cloudGraph`, `cloudGraph_adj`; adjacency is base adjacency, not a categorical product with an edgeless graph |
| Lemma 16 | `cloudGraph_vertex_count`, `cloudGraph_edge_count`, `paperGraph_counts`, `family_scaling`; exact corrected counts |
| Definition 17 | `liftedFault`, `liftedFault_not_target`; cloud lift of the full matching with only the protected lifted edge deleted |
| Lemma 18 | `liftedFault_degree_bound` applied to `matchingGraph_degree_bound` |
| Theorem 19 | `incidence_cloud_spanner_eq`, `paperGraph_spanner_eq`; concrete graph with no remaining geometric premises |

Theorem 2 (Althöfer et al.) and Theorem 4 (Bodwin–Haeupler–Parter) are cited
background results, not dependencies of the new lower-bound proof. Their
weighted upper bounds and conditional girth-conjecture statements are outside
this formalization's scope. No bibliography/survey formalization is claimed.
The [machine-readable statement map](verification/statement-map.json) records the exact correspondence. The composed mappings for Lemmas 10 and 13 passed the same independent semantic review as the direct declarations.

## Complete module index

`DegreeFaultSpanners.lean` imports all 18 implementation modules below.
The complete aggregate and every implementation module passed all local verification gates.

| Module | Responsibility |
|---|---|
| `FaultSpanner` | Fault semantics, extended-distance equivalence, edge forcing, stretch-one repair |
| `Incidence` | Actual affine subset-lines, bipartite graph, exact cardinalities |
| `SlopeAlgebra` | Distinct-slope independence and grouped coefficients |
| `GeometryWalk` | Alternating-walk encoding, multiplicity, cycle slope bounds |
| `ShortReach` | Sparse transverse displacement and endpoint uniqueness |
| `Construction` | Actual fault graph and augmented matching |
| `PathStraightening` | Restricted/transverse paths and exact Definition 8 bridge |
| `CycleObstruction` | Encoded short-cycle failure-edge lemma |
| `Blowup` | Cloud counts, lifted faults, surviving projection, general forcing |
| `ObstructionAssembly` | Concrete incidence obstruction and Theorems 14/19 |
| `Parameters` | Exact family scaling and complete-graph inequality |
| `RealBound` | Family integer-power to real-exponent conversion |
| `PaperTheorem` | Explicit graph family and corrected Theorem 5 |
| `AllSizesParameters` | Nearby prime, integer rounding, and common all-size factor |
| `DenseWitness` | Bounded-degree clique witnesses at every admissible size |
| `Padding` | Isolated-vertex padding, exact edge counts, preservation of forcing |
| `AllSizesRealBound` | General positive-factor real-exponent conversion |
| `AllSizesTheorem` | Every-size theorem and uniformly quantified positive constant |

## Verification

Verified on 9 October 2026 using Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- All 18 modules and the aggregate compile with `autoImplicit=false`; the normal
  `lake build DegreeFaultSpanners` also passes (2,476 jobs).
- The aggregate import index exactly covers all 18 implementation modules.
- The axiom audit inspects all 440 declarations by their defining module,
  including private/generated declarations, and permits only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The unmodified official Lean checker replays every implementation module and
  the aggregate separately through the kernel. The sequential driver invokes
  the same `LeanChecker.replayFromImports` function as the official CLI.
- An independent [semantic review](verification/SEMANTIC_REVIEW.md) and source-hash confirmation
  match the actual definitions, proof chain and all-N contract to the pinned
  source and documented repair. All 19 release source hashes match the review.

Run from the repository root:

```sh
lake exe cache get
lake build DegreeFaultSpanners
lake env lean "Unconditional Lower Bounds for Degree Fault Tolerant Spanners/verification/AxiomAudit.lean"
lake env lean "Unconditional Lower Bounds for Degree Fault Tolerant Spanners/verification/KernelReplayExact.lean"
```

The shared repository scripts also check every paper's module index, declared
axioms and kernel replay. This verified scope is the paper's new lower-bound
argument and its necessary fidelity bridges, with the explicit source correction;
it does not claim to formalize the cited background Theorems 2 and 4.
