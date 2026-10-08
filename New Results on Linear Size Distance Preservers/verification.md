# Verification record

Prepared on 8 October 2026 against published GitHub main commit
[`c4af45c0532038baef901cd82ef510910b91522a`](https://github.com/gbodwin/paper-formalizations/commit/c4af45c0532038baef901cd82ef510910b91522a)
of `gbodwin/paper-formalizations`. That upper-bound snapshot passed
[GitHub Actions run 37785506656](https://github.com/gbodwin/paper-formalizations/actions/runs/37785506656).
The user authorized publication of this lower-bound extension. The earlier
CI run does not cover it; use the workflow attached to the new commit for
its exact-head CI result.

## Current proof scope

Theorems 1 and 2 retain their proved finite statements. Theorem 1 uses finite
nonnegative weights and proves `3n + 24p floor(cuberoot(n))²`; Theorem 2 proves
`2p + 12 matchingNumber V`. Neither takes path selection, tree existence,
cut existence, or a counting estimate as an input. The defined induced
matching extremal quantity is proved subquadratic using mathlib's
triangle-removal theorem. Signed or infinite edge weights are outside the
unconditional Theorem 1 statement.

The lower-bound package has sixteen added proof modules relative to the
base, with the following results:

- Native weighted shortest-path attainment and edge forcing for arbitrary
  preserving subgraphs, using the actual list-walk infimum distance.
- A positive, symmetric, quadratically weighted repair of the modular
  Theorem 5 construction, with unique shortest paths, exact edge ownership,
  path incidence, and the universal `knx` subset-preserver edge count.
- The actual obstacle-product graph and native walks, exact counts, and a
  decomposition of every outer-to-outer walk using at most two connectors.
- Unweighted product uniqueness from inner native-path uniqueness and
  outer two-port uniqueness. The product uniqueness is proved, not assumed.
- A general theorem for the stated normalized integer weights: multiplying
  primary weights by `M` greater than each designated inner cost establishes
  unique shortest product walks. This is not the fully general real-weight
  epsilon formulation of Lemma 7.
- All hypotheses of that weighted theorem discharged for modular inputs
  satisfying `(k+1)x≤n` and `3nx≤σ`. The weaker structural bounds `x≤n` and
  `nx≤σ` alone are not claimed sufficient for metric uniqueness.
- `ModularObstacle.preserver_edge_count`: every subset preserver on the
  `2σ` outer terminals keeps all `σnx(k+2)` edges of the graph with
  `2σ+σ(k+1)n` vertices. Actual weights are finite, positive, and symmetric.
- `TheoremThree.family_lower_bound`: for every `k≥0, x>0`, a concrete graph,
  weight function, and terminal set with `n=(k+1)x`, `σ=3(k+1)x²` satisfy
  `T³N²≤648E³` for every preserving subgraph. The coefficient is uniform.
- `DirectionGraph.canonical_unique`: actual unweighted modular vector
  graphs have unique designated shortest paths under bounded coordinates,
  the explicit no-wrap bound, and the geometric `AverageRigid` condition.
  `sphere_rigid` proves that condition for common-sphere directions.

**Theorems 3–4 are not both complete.** For Theorem 3, the finite witnesses
and the growth rate on the displayed family are verified; arbitrary-size
rounding/padding and coverage of the full parameter range remain. For
Theorem 4, the sharp lattice-direction existence/cardinality theorem,
the general strict-convexity bridge, graph count/incidence connections,
and final parameter assembly remain. The common-sphere special case does
not silently replace the required sharp geometric result.

No missing obligation is represented by an axiom or admission. The checked
counterexample to the paper's displayed Euclidean weighting is retained;
it refutes that weighting, not the existential weighted theorem.
The [coverage table](README.md#proof-map-and-remaining-scope) is part of the
verification claim.

## Checks on this extension

| Check | Result |
| --- | --- |
| Lean | 4.34.0, release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435`; lockfile unchanged |
| Full repository build | Passed, both libraries; 3,269 jobs |
| Module indexes | Both passed; 34 distance-preserver modules and 13 VFT modules |
| Module-origin axiom audit | 806 distance-preserver declarations and 195 VFT declarations passed |
| Allowed axioms | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Sequential native kernel replay | CI runs `scripts/KernelCheck.sh` for all 47 project modules; independent replays of `TheoremThree` and `DirectionGraph` passed |
| Dependency checkouts and source/whitespace review | All nine match the unchanged lockfile and have clean tracked files; no proof holes, custom axioms, unsafe declarations, or native decision shortcuts in the sixteen added proof modules; whitespace check passed |

The axiom audit examines every declaration by its defining module,
including private and generated declarations. Both libraries must contribute
declarations. The major newly exported lower-bound results are also printed
explicitly in `scripts/AxiomAudit.lean`.

Kernel replay uses Lean's own kernel and imported dependency environments.
It is not an independently implemented checker or a rebuild/replay of every
mathlib dependency. Non-fatal style and deprecation warnings remain.

## Independent skeptical review

The prior foundations review compiled all eleven then-added modules,
replayed five selected modules with `leanchecker`, and repeated the full
axiom audit. It found no false proved statement or verification failure,
but correctly rejected any claim that this verified Theorems 3–4.
It supplied the endpoint-collision example for the weak structural bounds
recorded in the README. The new metric proof adds the stronger no-wrap
bounds and does not attempt to derive uniqueness from those weak bounds.

A new independent skeptical reviewer compiled all five new product/family/
vector modules, replayed `TheoremThree` and `DirectionGraph` through the
kernel, and ran eighteen targeted transitive axiom checks. All passed with
only the standard three axioms. Concrete applications of the family theorem
at `(k,x)=(1,1)` and `(10,3)` compiled without graph, uniqueness, or attainment
assumptions. The reviewer independently checked `12E=(k+2)T²`, confirming
that the forced-edge/terminal-pair ratio grows with `k`.

The reviewer found **no correctness blocker in the stated finite results**.
It verified the walk-distance semantics, coverage of backtracking/repeated
vertices, integer separation gap, actual undirected edge counts, exact
terminal cardinality, and inherited weights in the preserver quantifier.
It emphasized all of the scope limitations above: the family is not the
arbitrary-size Theorem 3 statement; the integer theorem is not general
real-weight Lemma 7; `AverageRigid` and its sphere special case do not supply
the sharp lattice theorem or Theorem 4. The quadratic weights repair the
construction rather than validate the printed Euclidean weighting.

The reviewer did not rebuild mathlib or use a separate implementation of
Lean's kernel. No repository source was changed by the review.

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
