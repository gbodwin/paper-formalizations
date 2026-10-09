# Concurrent flow and the normalized sparsest LP

Source: arXiv:2604.03412v3, intro.tex:314–325. This is the explicitly normalized
interpretation needed to turn assignment rounding into an optimization statement.
It does not identify its W with an unspecified normalization in the source.

## Finite model and exact identification

For each demand d there is a finite type Path(d) of actual directed simple paths.
A path uses each internal vertex (vertex model) or directed edge (edge model) once.
The generic core also allows natural multiplicities. A joint profile q chooses
one actual path for each demand. Its resource incidence is SUM_d a(d,r,q(d));
shared resources are counted with multiplicity, not replaced by their union.

A packing F of joint profiles gives path amounts by marginalization. Every demand
then receives the same throughput lambda = SUM_q F(q), and total resource loads
are identical. Conversely, for positive equal throughput lambda, use
F(q)=lambda PRODUCT_d (f(d,q(d))/lambda). Finite distributivity proves both total
mass and marginal identities. At zero throughput use the zero profile packing.
Excess per-demand flow can be discarded, proving equivalence with maximizing the
minimum, rather than sum, of delivered demand amounts.

IntegerPackingCovering extends the existing separation proof to natural incidence.
ConcurrentProfiles proves the product/marginal equivalence. No strong-duality
axiom or LP-duality premise is introduced.

## Domain and degeneracies

- An unreachable demand has no path. It forces concurrent throughput zero; the
  empty cut separates it at zero cost. No infinite distance is coerced to a finite
  value and included in a normalized denominator.
- For all-reachable demands, a profile cover is feasible exactly when every
  profile uses a resource. Equivalently, some demand has no zero-resource path.
- If every demand has a zero-resource path, common throughput is unbounded and
  all demanded distances are identically zero for every length assignment.
  The positive-normalization LP is infeasible. This includes the empty-demand
  family. It must not be assigned a finite optimum or positive sparsity ratio.
- Some individual zero-resource demands are allowed. Unlike fractional multicut,
  fractional sparsest-cut feasibility does not require every demand to be costly.
- Zero capacities and zero optimum objectives remain valid in the feasible domain.

## Normalization

The joint-profile dual requires every profile to have length at least one.
Choosing an actual shortest path separately for each demand identifies this
constraint exactly with S=SUM_d distance_w(d) >= 1. Attained strong duality gives
lambda=C at the S=1 normalization. Scaling preserves C/S and permits S=m>0.
In average-distance-one normalization, lambda=C/m, never C. The relevant mass is
W_avg=m SUM_r w(r)/S; for S=m it is the optimizer's actual raw total length.

A gap theorem can choose any attained normalized optimizer, apply the verified
SparsestVertexCorollary or SparsestEdgeCorollary to that optimizer, and use the
mass of that same optimizer. No claim of optimizer-independent mass is needed.

## Verification status

All five modules passed strict Lean compilation with `-j1`, `-DautoImplicit=false`,
and `-DwarningAsError=true` on 9 October 2026. Every one of their 170 owned
declarations passed a recursive axiom audit allowing only `propext`,
`Classical.choice`, and `Quot.sound`. Each exact module passed an isolated
`LeanChecker.replayFromImports` invocation. Source hashes, counts, commands and
preserved logs are in `verification/concurrent-duality/manifest.json`; the
reproducible verification driver is `verification/concurrent-duality/verify.py`.

An independent semantic review checked multiplicities, common-throughput versus
sum-flow semantics, actual shortest paths, zero-cost normalization, masked
nonedges, and all stated degeneracy cases before compiler verification.

## Theorem map

- `IntegerPackingCovering.strong_duality`: attained natural-incidence packing /
  covering duality, derived from finite-dimensional geometric separation.
- `ConcurrentProfiles.concurrent_iff_profile_packing`: exact equivalence between
  joint-profile packing and equal-throughput actual path flows.
- `ConcurrentProfiles.exists_concurrent_iff_atLeast`: equivalence with maximizing
  the conventional minimum delivered demand amount.
- `ConcurrentDuality.exists_solution`: attained maximum concurrent flow and
  minimum fractional sparsest ratio from any positive-distance feasible witness.
- `ConcurrentDuality.positive_normalization_iff`: exact finite-distance domain;
  `concurrent_unbounded_of_free_profile` and `distanceSum_eq_zero_of_free_profile`
  cover the structural all-free case without assigning it a finite optimum.
- `ConcurrentVertexFlow.exists_solution` / `ConcurrentEdgeFlow.exists_solution`:
  instantiate the finite theorem with actual directed simple paths and the
  existing graph distance/objective definitions.
- The graph modules' `ratio_minimal`, `objectives_eq`, `averageWeight_distanceSum`,
  `averageWeight_mass`, and `averageWeight_objective` give the exact optimizer,
  normalization, W parameter and lambda=C/m interpretation.
- The graph modules' `sparsest_gap_uniform` apply verified normalized rounding to
  every chosen attained optimum, with constants fixed before the graph, costs,
  demand family and optimizer. The bound's fractional objective equals the
  maximum concurrent throughput by `objectives_eq`.
- Both graph modules' `unreachable_zero_optimum` prove feasible zero flow,
  maximal common throughput zero, and an empty zero-cost cut separating at least
  one demand when a demanded pair is unreachable.

No polynomial-time construction or runtime bound is asserted by these modules.
The printed source's unspecified W normalization remains a documented source
ambiguity; the explicit average-normalized theorem is fully proved.
