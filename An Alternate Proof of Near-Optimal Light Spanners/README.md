# An Alternate Proof of Near-Optimal Light Spanners

Lean formalization of Greg Bodwin's paper, TheoretiCS 4 (2025), Article 2.
Source: https://arxiv.org/abs/2305.18647v6
DOI: https://doi.org/10.46298/theoretics.25.2

## Main-result checkpoint

The entire connected-graph main-result pipeline now compiles with Lean 4.34.0,
including the implemented sorted greedy construction, graph reductions, bucket
walks, hiker construction, deletion counting and finite independent sampling.
The aggregate verification record is
[verification/MAIN-RESULT-VERIFICATION-2026-10-10.md](verification/MAIN-RESULT-VERIFICATION-2026-10-10.md).
At checkpoint creation, exact-commit CI and the fresh independent skeptical
end-to-end audit are pending. Subsequent CI status is attached to the exact
GitHub commit; the companion records later audit/publication status. No public
completion claim is based solely on compilation.

`near_optimal_greedy_spanner` proves that the actual greedy output, at stretch
`(1+epsilon)(2k-1)`, has both walk and shortest-distance stretch, contains an
actual minimum spanning tree of the input, and has lightness at most

    8 + (2048/epsilon) n^(1/k).

`near_optimal_greedy_lightness` gives the usual fixed-epsilon coefficient
`(8+2048/epsilon)n^(1/k)`. These assertions hold for every epsilon>0 and
integer k>=1 on a finite connected graph with globally nonnegative weights
and strictly positive weights on graph edges. Sorting, an MST, graph reductions,
dispersion, bucket enumeration, hiker occupancy and counting identities are
all proved internally, rather than supplied as assumptions.

`exists_near_optimal_spanner` needs positivity only on actual graph edges:
it constructs a nonnegative extension off the graph and transfers all relevant
walk, tree and weight quantities back. Its conclusion is existence; it does
not claim the extended greedy run is definitionally the unextended run.

## Scope and source corrections

The source's Definition 1.3 footnote explicitly permits assuming connectivity
for its MST convention. Disconnected minimum-spanning-forest assembly is not
formalized here. The singleton case uses totalized zero division. Cited prior
work and conditional lower-bound tightness are not reproved. The unused
Section 2 and Section 4 intermediate counting expositions are not all separately
formalized. This is an end-to-end main-result formalization in its stated
connected-MST domain, not a claim to prove every displayed statement literally.

[verification/STATEMENT-COVERAGE.md](verification/STATEMENT-COVERAGE.md) maps
all 52 displayed statement/proof/solution blocks to proofs, repaired statements,
or explicit omissions. It has a machine-readable JSON companion.
[verification/SOURCE-CORRECTIONS.md](verification/SOURCE-CORRECTIONS.md) records:

1. The subdivision argument needs a global vertex budget, not a false pointwise
   lower bound of one half on pre-existing tree edges.
2. Lemma 3.7's strict weight bound applies to chords; all edges need a maximum
   with one.
3. The hiker protocol uses t+1 chord layers and t shuttle moves, repairing the
   subunit floor case.
4. A finite bound uniform over all positive epsilon requires a unit-cycle
   baseline. Theorems 4.1/5.1 have actual canonical-cycle counterexamples under
   the uniform reading. Fixed-epsilon asymptotics and the explicitly O_epsilon
   main theorem are unaffected.

The repaired finite-uniform Theorem 5.1 is

    weight(H) <= n + (8/epsilon)n*n^(1/k).

For 0<epsilon<=1, the usual no-baseline form holds with constant 9. No hidden
small-epsilon hypothesis enters the unrestricted main theorem.

## Main proof declarations

- `greedyOutput_preliminaries`: actual sorted greedy graph, shortest-distance
  stretch, weighted girth, Kruskal/MST containment with equal-weight ties.
- `unit_spanning_cycle_reduction_of_mst`: actual graph on at most 4n−4 vertices,
  preserved girth threshold and at least one-quarter lightness; spanning tree
  tour, vertex copies, positive scaling, repeated subdivision and rounding.
- `BucketSafe.unique_of_chordDarts`: Claim 2, actual oriented chord words and
  a common terminal vertex determine the walk.
- `BucketMonotoneKPath.chordEdges_nodup`: Claim 3, exactly k distinct chords.
- `BucketMonotoneKPath.unique`: Lemma 5.5, actual endpoint uniqueness.
- `UnitSpanningCycle.weak_counting`: Lemma 5.8, actual finite buckets, hiker
  walks and endpoint permutations; original ambient safety budget k retained.
- `exact_extra_safe_of_long`, `useful_family`, `medium_counting`: actual
  truncation, injective padded endpoint families and deletion induction.
- `FiniteSampling.sum_mass_containing`, `expected_sum`, `endpoint_survival`:
  finite powerset Bernoulli weights, exact normalization, expectation and p^k
  survival. No probabilistic identity is assumed.
- `UnitSpanningCycle.full_counting`: Lemma 5.13 with threshold 5n/epsilon and
  lower bound `(n/4)*(epsilon*offcycleWeight/(5n))^k`.
- `unit_cycle_weight_bound`, `weighted_girth_lightness_bound`,
  `near_optimal_greedy_spanner`, `exists_near_optimal_spanner`: the final joins.

## Reproducibility

The repository pins Lean 4.34.0 and mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. All proof modules compile with
`autoImplicit=false`. There are no `sorry` proofs, project axioms or assumed
substitutes for the main combinatorial steps. Harmless linter warnings remain.
The all-declarations audit includes private/generated declarations and permits
only `propext`, `Classical.choice`, and `Quot.sound`.

From the repository root:

```sh
lake exe cache get
lake build LightSpanners
bash scripts/CheckModuleIndex.sh
lake env lean "An Alternate Proof of Near-Optimal Light Spanners/verification/AllDeclarationsAudit.lean"
lake env lean "An Alternate Proof of Near-Optimal Light Spanners/verification/SelectedAxioms.lean"
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The preceding 42-module/672-declaration hiker checkpoint passed full CI at
[03fcbd7a](https://github.com/gbodwin/paper-formalizations/actions/runs/38066461206).
Earlier exact milestones and semantic reviews remain in `verification/`.
This package does not import other paper libraries. Code uses the repository
MIT license; the mathematical paper is CC BY 4.0.
