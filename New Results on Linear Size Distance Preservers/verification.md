# Verification record

Prepared on 7 October 2026 against published GitHub `main` commit
[`140dd136b796881bbacb9ba36767b3f70cc62559`](https://github.com/gbodwin/paper-formalizations/commit/140dd136b796881bbacb9ba36767b3f70cc62559)
of `gbodwin/paper-formalizations`. That earlier partial package passed
[GitHub Actions run 37668884837](https://github.com/gbodwin/paper-formalizations/actions/runs/37668884837).
The remote was reread after implementation and still pointed to this base.

This record covers the extension implementing Theorems 1 and 2. The checks
below were recorded during its preparation on 7 October. Publication was
authorized on 8 October; the saved patch applied cleanly to the same published
base. Fresh GitHub CI now also runs `scripts/KernelCheck.sh` after the build,
module-index checks, and declaration-level axiom audit. The earlier GitHub
Actions run does not cover these new files; consult the run for the exact
published commit for the fresh verification result.

## Checks performed

| Check | Result |
| --- | --- |
| Lean | 4.34.0, release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435`; unchanged |
| Dependency checkouts | All nine match the unchanged lockfile; tracked files clean |
| Full repository `lake build` | Passed, both libraries; 3,253 jobs in the reported build graph |
| New module index | All 18 distance-preserver proof modules imported, including ten added modules |
| Both module-index checks | Passed |
| Module-origin axiom audit, distance-preserver library | All 375 declarations passed |
| Module-origin axiom audit, existing VFT library | All 195 declarations passed |
| Main theorem type inspection | Theorems 1 and 2 take graph, weights where applicable, and demands; no path-selection or counting hypotheses |
| Exported theorem axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound`, or a subset thereof |
| Sequential Lean kernel replay | All 31 proof modules passed: 13 VFT and 18 distance-preserver modules |
| Source review | No admitted proofs, custom axioms, unsafe declarations, or native-decision proof shortcuts in the added proof modules |
| Whitespace and patch applicability | `git diff --check` and application check against the published base passed |

The audit checks declarations by their **defining module**, including private
and generated declarations. Both libraries must contribute declarations.
The main upper bounds, consistent-subpath theorem, lazy-tree construction,
branching count, favorable-cut existence, and imported-removal consequence
are also printed explicitly by the audit script.

Kernel replay uses Lean's own kernel and imported dependency environments.
It is not an independently implemented checker or a rebuild/replay of every
mathlib dependency. The source contains some non-fatal style/deprecation
warnings; all build and proof-checking gates passed.

## Mathematical scope

`LinearDistancePreservers.theorem_one` proves the explicit bound
`3n + 24p floor(cuberoot(n))²` for finite directed graphs with finite
nonnegative weights. It handles zero weights, self-loops, empty vertex sets,
and unreachable demands. It constructs a minimum path by lexicographic
original-cost/edge-code minimization, proves consistency, extracts `Routing`,
and proves that its union preserves the original list-walk infimum distance.
Signed weights and infinite edge weights are outside this unconditional
statement. The older conditional theorem with extended weights is retained.

`LinearDistancePreservers.theorem_two` proves a subgraph with at most
`2p + 12 matchingNumber V` undirected edges and equal demanded extended
unweighted distances. Its input is any finite simple undirected graph and
any finite demand set. Lazy trees, the `2|D|` branching bound, the favorable
cut, edge assignment, and induced-matching count are all proved internally.

`matchingNumber V` is the defined maximum edge count of a simple graph on
`V` admitting a partition into at most `|V|` induced matchings. The
orientation-based representation counts each undirected edge once and
explicitly enforces endpoint disjointness and absence of cross edges.
`matchingNumber_subquadratic` proves the standard epsilon/threshold form of
`M(n) = o(n²)` through an explicit tripartite reduction to mathlib's
triangle-removal theorem. It does not postulate an extremal estimate or
confuse the induced-matching normalization with mathlib's triangle-count
Ruzsa–Szemerédi number.

The [coverage table](README.md#proof-map-and-remaining-scope) is part of the
verification claim. Theorems 3–4, the obstacle product, and the unweighted
lower-bound construction remain incomplete. The earlier checked construction
counterexample and quadratic-weight repair are preserved.

## Local reproduction detail

The standard Lean release used the same executable-discovery compatibility
adjustment as the previous reproduction: `/proc/.../exe` readlink requests
were redirected to `/proc/self/exe`. It affects executable discovery, not
Lean's kernel or proof terms. The runtime and helper are temporary environment
files and are not part of this patch. GitHub CI uses its normal runner.
