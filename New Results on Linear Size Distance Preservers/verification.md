# Verification record

## Sharp planar continuation, 10 October 2026

The two new modules `PrimitiveDirections` and `PlanarProduct` pass the full
build, module indexes, complete axiom audit, and sequential kernel replay
at exact source commit `034620ea79740a0efa4ba3bc4706c37dff773f67`.
[CI run 38052458003](https://github.com/gbodwin/paper-formalizations/actions/runs/38052458003)
completed successfully. The run replayed all 85 project modules.

The elementary primitive-slope count gives the sharp planar growth rate,
and the graph bridge constructs exact-size unweighted witnesses from solely
numerical capacity conditions. Independent semantic review found no blocker.
See the [completed checkpoint record](verification/planar-continuation.md)
for exact scope, audit counts, provenance, and the distinction between CI,
local partial checks, and semantic review. **Full Theorem 4 remains incomplete:**
higher-dimensional sharp geometry and full parameter selection remain.
The records below retain their historical scope and dates.

## Theorem 4 extension and recovery, 9 October 2026

**Theorem 4 is not yet proved end to end.** Five new modules construct
finite unweighted witnesses and verify an obstruction to the printed final
rate implication. They assume no graph uniqueness or lower-bound conclusion:

- `BehrendPorts`: actual progression-free outer slopes, using mathlib's
  quantitative Behrend theorem or its integer sphere/digit construction.
- `SphereDirections`: injective bounded inner directions on a common
  sphere, with average rigidity proved internally.
- `UnweightedPadding`: exact native `edist` correspondence in every
  subgraph, terminal enlargement, and preservation of forced edges.
- `BehrendProduct`: a graph on exactly `N` vertices with exactly `T`
  terminals, from solely numerical conditions; every subset preserver
  keeps exactly `M n^d x (k+2)` edges.
- `TheoremFourRateAudit`: a dimension-uniform rate inequality and a
  log/real-power bridge to the expression in the paper.

See the README for the complete numerical hypotheses and remaining scope.
The common-sphere bound is weaker than the sharp fixed-dimension lattice
bound. That sharper geometry, its dimensional constants, and global
parameter selection remain open. Padding itself is now proved.

### Independent skeptical review

The reviewer independently compiled all five modules and replayed them
through Lean's kernel. Thirteen targeted axiom checks found only
`propext`, `Classical.choice`, and `Quot.sound`. It found no source blocker,
circular uniqueness premise, or undeclared geometric input in the finite
numerical construction.

A nondegenerate application compiled at
`d=3,r=3,x=2,n=6,k=1,q=14,b=2,M=3^15,N=434M,T=2M`. This uses two distinct
inner directions, positive inner depth, and exact-size padding together.

The reviewer did **not** certify full Theorem 4. It confirmed that, for
`L=log N` and `t=(2/3)L-log sigma`, the logarithm of the displayed
polynomial factor divided by `sigma²` is at most `27t²/(8L)`, uniformly
for `d≥1,L>0`. For `0≤t≤K sqrt L`, a uniform loss `exp(-c sqrt L)`
therefore gives a ratio at most `exp(27K²/8-c sqrt L)`. For fixed `K` and
positive `c`, this tends to zero. The pointwise inequality and the literal
power correspondence are kernel-checked; a separate named limit theorem
is not included.

This shows that the displayed lower bound does not imply the printed
near-`N^(2/3)` superquadratic corollary. It is **not a graph upper bound
and not a disproof of the existential theorem**. Keeping the outer density
loss `F` explicit retains a factor `F^(-(1-1/d))`; the reviewer found no
cancellation in the presented construction estimates. A deficit on the
`(log N)^(3/4)` scale is suggested by balancing those estimates, but no
replacement theorem or uniform parameter proof is claimed here.

### Verification provenance and interrupted publication

Before the interruption, the complete three-library build passed (3,373
jobs), all 62 project modules passed kernel replay, and the module-origin
audit passed for 975 distance-preserver, 195 VFT, and 48 LightSpanners
declarations. All nine dependencies matched the lockfile. The new module
indexes and staged whitespace check also passed. These are historical
local results, not substitutes for checking a recovered revision.

Publication was interrupted before a commit was confirmed. Automated
workspace maintenance then removed the unpublished checkout. The five
source files were reconstructed from the session's edits; all five match
the recorded character counts. This is weaker provenance than an original
cryptographic source snapshot, so **fresh exact-commit CI is required**.
The attached GitHub workflow is the authority for validation of this
recovered revision; earlier logs alone do not certify it.

The recovery starts from main commit
`8d7295fd8d86b3d1be0881064ec56a03e840f659`, preserving the independently
added LightSpanners and DegreeFaultSpanners packages and their shared
verification hooks. Source hashes are recorded in
`verification/theorem4-source-hashes.json`.

### Complete-graph baseline

`UnweightedClique.clique_lower_bound` adds an exact arbitrary-size baseline:
for `0 < T ≤ N`, it constructs an unweighted graph on `Fin N` and a terminal
set of cardinality `T`; every subgraph preserving all terminal `edist`
values has exactly `T.choose 2` edges. The source proof observes that
preserving distance one forces each clique edge, then uses the verified
padding theorem. This is not a substitute for the remaining sharp geometry.
Validation of this additional module is the workflow attached to its commit;
the historical five-module review above does not cover it.

### Small-deficit range of the displayed bound

`TheoremFourDense.displayed_bound_of_small_deficit` combines the literal
rate inequality with the clique witness. Its inputs are only numbers:
`2≤T≤N`, `d≥1`, `K≥0`, `0≤(2/3)log N-log T≤K sqrt(log N)`, and
`27K²/8+log 4≤c sqrt(log N)`. It produces an actual graph on `Fin N`
and exactly `T` terminals, and lower-bounds the edge count of every
preserver by the displayed real-power expression including
`exp(-c sqrt(log N))`. The proof establishes that the expression is at
most `T²/4≤T.choose 2` under those hypotheses. This is a completed
subcase only when the attached exact-commit checks pass, not a claim that
the sharp lattice estimate or full Theorem 4 has been formalized.

## Earlier verification snapshot

Prepared on 8 October 2026 against published GitHub main commit
[`558ba83dd011bc63062b1b1b716f877b327f2f68`](https://github.com/gbodwin/paper-formalizations/commit/558ba83dd011bc63062b1b1b716f877b327f2f68)
of `gbodwin/paper-formalizations`. That earlier snapshot passed
[GitHub Actions run 37841280490](https://github.com/gbodwin/paper-formalizations/actions/runs/37841280490).
This extension adds seven proof modules. The earlier CI run does not cover
them; use the workflow attached to the commit containing this record for
its exact-commit CI result. The user authorized publication.

## Historical proof scope (8 October extension)

Theorems 1 and 2 retain their proved finite statements. Theorem 1 uses finite
nonnegative weights and proves `3n + 24p floor(cuberoot(n))²`; Theorem 2 proves
`2p + 12 matchingNumber V`. Neither takes path selection, tree existence,
cut existence, or a counting estimate as an input. The defined induced
matching extremal quantity is proved subquadratic using mathlib's
triangle-removal theorem. Signed or infinite edge weights are outside the
unconditional Theorem 1 statement.

**Theorem 3 now has an arbitrary-size finite statement covering every
fixed constant in its claimed parameter range.**
`TheoremThree.bounded_range_lower_bound` takes only positive natural `C`,
`2≤T≤N`, and `T³≤C³N²`. It constructs an actual undirected graph on `Fin N`,
finite positive symmetric edge weights, and exactly `T` terminals. Every
subgraph preserving all distances between those terminals has

```
T³N² ≤ (32768C)³ |E(H)|³.
```

Equivalently, its edge count is at least `T N^(2/3)/(32768C)`. Any fixed
real big-O range constant can be bounded by a positive natural `C`.
`exact_size_lower_bound` gives constant `8192` when `T³≤N²`. The Lean
statements use integer powers, not named asymptotic or real-power notation.
They assume no rigidity, path uniqueness, attainment, or edge-count bound.

`PreserverPadding` proves distance preservation under injective padding in
every subgraph, exact edge-count preservation, and terminal enlargement.
`PathLowerBound` handles the small-terminal regime with an endpoint pair
forcing all `N−1` path edges. `LowerBoundParameters` checks floors, capacity,
vertex budgets, and the uniform rate. `TheoremThreeExact` assembles the
witnesses. `T≥2` is necessary: one terminal imposes only zero self-distance.
For zero terminals the lower bound is zero. Padding may add isolated
vertices, which the paper's graph definition permits.

The weighted construction uses the verified quadratic repair. The checked
counterexample to the displayed Euclidean weighting remains: it refutes
that weighting, not the existential theorem. The specialized integer
separation theorem suffices for Theorem 3; the fully general real-weight
formulation of Lemma 7 is not claimed proved.

**Theorem 4 is still not proved end to end.** This extension proves:

- `DirectionPerfect`: actual vector-graph vertex/path/edge counts, simple
  canonical paths, unique edge ownership, and exact indexed path incidence.
  `canonical_support_injective` proves distinctness when `k>0`. For `k=0`
  several labels can denote the same singleton path.
- `ConvexRigidity`: exclusion from the convex hull of the other vectors
  implies `AverageRigid`. This is sufficient for the native shortest-path
  proof and follows from the paper's stronger coefficient-sum≤1 condition.
- `DirectionObstacle`: both product metric hypotheses are discharged from
  two bounded, injectively indexed convex-position direction families.
  The inner paths index the outer directions, making port capacity explicit.
  Every subset preserver of the `2 M^|Q|` outer terminals keeps all
  `M^|Q| n^|D| |J| (k+2)` edges. Distances are mathlib's actual `edist`.

The missing obligations are the sharp convex-lattice direction-set
existence/cardinality bound and the final dimension, port-size, and
arbitrary-size parameter selection for Theorem 4. No conditional count,
common-sphere estimate, custom axiom, or admitted proof replaces them.
The [coverage table](README.md#proof-map-and-remaining-scope) is part of the
verification claim.

## Historical checks (8 October extension)

| Check | Result |
| --- | --- |
| Lean | 4.34.0, release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435`; lockfile unchanged |
| Full repository build | Passed, both libraries; 3,276 jobs |
| Module indexes | Both passed; 41 distance-preserver modules and 13 VFT modules |
| Module-origin axiom audit | 939 distance-preserver declarations and 195 VFT declarations passed |
| Allowed axioms | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Sequential native kernel replay | Passed for all 54 project modules; final source includes the positive-layer path injectivity theorem |
| Dependencies | All nine checkouts match the lockfile and have clean tracked files |
| Source review | No proof holes, custom axioms, unsafe declarations, or native decision shortcuts in the seven new modules; whitespace check passed |

The axiom audit examines every declaration by its defining module,
including private and generated declarations. Both libraries must contribute
declarations. Major results are also printed explicitly in
`scripts/AxiomAudit.lean`. An initial audit encountered stale root-module imports and rejected the
new identifiers. Rebuilding the root and repeating the audit passed with
all new declarations included.

Kernel replay uses Lean's own kernel and imported dependency environments.
It is not an independently implemented checker or a rebuild/replay of every
mathlib dependency. Non-fatal style and deprecation warnings remain.

## Independent skeptical review

The independent reviewer compiled all four new Theorem 3 files, replayed
all four with `leanchecker`, and ran eight targeted transitive axiom checks.
Concrete applications compiled at `(N,T,C)=(2,2,2)`, `(8,8,2)`, and a large
choice above the path threshold. All checks passed using only the standard
three axioms. The reviewer also compiled the zero self-distance fact
underlying the necessary one-terminal exception.

The reviewer found **no blocker** and explicitly confirmed that
`bounded_range_lower_bound` closes the former arbitrary-size/range gap.
The padding and terminal enlargement arguments preserve the original
forcing constraints, and the final theorem contains no hidden construction
assumption. Its remaining qualifications are the explicit cubed notation,
permitted disconnected padding, and the documented repaired weighting.

For Theorem 4, the reviewer independently compiled all three new files,
replayed all three through the kernel (including another DirectionPerfect
replay after the distinctness lemma), and ran ten clean targeted transitive
axiom checks. It found no source blocker or circular assumption in the
convexity, native uniqueness, exact counts, and S×S distance forcing.
An independent standard-basis proof supplied a nonempty concrete family
satisfying `ConvexPosition` and both product uniqueness properties, so
the hypotheses are jointly satisfiable. An independent positive-layer injectivity
proof confirmed the path-count convention. The single-layer qualification
is documented and formalized in `canonical_support_injective`.

The reviewer explicitly did not certify full Theorem 4: sharp lattice
cardinality, port capacity, and global parameter selection still have to
be proved. The ordinary convex-hull condition is a valid weakening of the
paper's stronger convexity condition, not a graph-uniqueness assumption.
No repository source is modified by the independent review.

## Reproduction

Run from the repository root:

```sh
lake build
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The local standard Lean release needs an executable-discovery compatibility
adjustment: `/proc/.../exe` readlink requests are redirected to
`/proc/self/exe`. It affects executable discovery, not the kernel or proof
terms. The runtime and helper are temporary environment files and are not
part of the repository. GitHub CI uses its normal runner.
