# Lower-certificate obstruction checkpoint — 10 October 2026

Status: active partial verification. Main upper/lower/runtime scope is incomplete.

## Exact CI-green reviewed baseline

Commit `30ff80ef6bf429d823bf14d84866f4ac1b996fe6` contains 21 modules and 229
project declarations. Its local root/index/build, exhaustive allowed-axiom audit,
all module kernel replays and frozen independent semantic reviews passed.
Full exact-commit CI passed, including repository-wide kernel replay:
https://github.com/gbodwin/paper-formalizations/actions/runs/38080374924 .

The preceding 19-module/219-declaration checkpoint
`e5bbdf892cba74f0a0be8b890f1da2daec065399` also passed full exact CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38079515337 .
The 16-module/171-declaration checkpoint
`827800bb20f1b59b896be0a0a1a5f5294f6dc788` passed full exact CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38077848156 .

The earlier 12-module/151-declaration commit
`e79a8b06353ed2155bca7080080724c5abfba193` also passed full exact CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38076966078 .
The initial four-module/65-declaration commit
`aedcf714c75ad2db7ee81ae3d0dc56e279155659` passed full exact CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38075342370 .

## New obstruction components

Three new modules add an actual six-vertex counterexample to the Theorem34
MST-cloud denominator certificate, a generic every-spanning-tree obstruction
including the exact source cloud rounding, and an exact high-fault saturation
lemma. Their 48 declarations passed standalone local axiom audit; all three
compiled and were independently kernel replayed. The source interpretation and
frozen statements have independent semantic review in
`FOURTH_SOURCE_AND_COMPONENT_AUDIT.md`.

The fixed-f certificate defect invalidates that proof step, not the lower
bound theorem itself. The infinite near-extremal family used to establish
source applicability is independently reviewed mathematics; its entire lambda
comparison is not claimed as formalized. The high-f lemma is exact finite only.
An f-dependent sufficiently-large-n threshold can avoid its diagonal examples,
so no unconditional asymptotic lower refutation is asserted.

Expanded 19-module aggregate build/root/index: PASS. Exhaustive allowed-axiom audit: PASS, 219 declarations. All three new exact sources had also passed independent kernel replay before being copied unchanged into this repository.
The 19-module/219-declaration checkpoint is published as
`e5bbdf892cba74f0a0be8b890f1da2daec065399`. Exact CI passed, including build/index/
all-declaration audit and repository-wide kernel replay:
https://github.com/gbodwin/paper-formalizations/actions/runs/38079515337 .

## New supplied-host and enlarged-cloud wrappers

Two further frozen modules, HostGraphSampling and LargeCloudCertificate, compile;
all10 new declarations pass exhaustive allowed-axiom audit, and both modules
pass independent kernel replay. Their semantic review is
FIFTH_SEMANTIC_REVIEW.md, frozen by FIFTH_SOURCE_HASHES.json.
The first actually joins the finite sample to the blocker/MST-pruned host graph
and proves a coarse per-host weight bound. It explicitly requires every
candidate blocker set to avoid the supplied spanning host tree. The coarse
ratio argument assumes at least two host vertices and strictly positive edge
weights. It does not construct global hosts or perform subtype transport.
The second proves the actual all-fault connectivity certificate for cloud size
strictly above q; the weaker resulting scaling does not restore Theorem34.
The 21-module aggregate build/root/index passed; all229 declaring-module declarations pass the allowed-axiom audit. Exact-commit CI passed at the frozen 30ff80e commit above.

## Covered mathematical content

Actual seeded greedy correctness, literal all-pairs distance semantics, genuine
minimum denominators, missing-edge degree/connectivity, actual greedy blocking,
finite host counting, blocker/MST graph pruning on a supplied spanning host,
finite Bernoulli weighted expectation and maximizing sample, actual bipartite
counterfamilies and unbounded square-root ratios, and the corrected explicit
coarse weighted-girth lightness estimate are checked components. No final bound,
probabilistic oracle or graph-packing theorem is inserted as an axiom.

## Remaining obligations

Eulerian Steiner-forest packing and its substantial multigraph/splitting/tree-
packing dependencies; global host construction and vertex-set transport; the
global host-family weight aggregation; optimized heavy/light sampling; a valid
replacement lower-bound certificate/construction; other lower bounds; randomized
conditioning/concentration and runtime; the source multigraph extension.

A supplied host tree is a genuine premise of the current pruning theorem.
WeightedSampling alone does not handle deterministic host-tree blockers; the
new host assembly explicitly requires those blockers avoid the host. The component
results do not imply a main theorem until these obligations are discharged.

No fresh whole-paper skeptical final audit has been requested, and no public
research-site link is implied by this partial checkpoint.

## New Section 4.1 cycle-construction foundations

Eight further modules have been frozen for local gates and independent review.
`ParallelSubdivision` defines actual degree-two branch vertices; different
`colorGraph` edge sets are disjoint. `DisjointCycleFaults` and
`SubdivisionCleanColor` prove that fewer than twice the number of colors in
faults leave a color with at most one failed graph edge, then localize that
failure to one base edge. `SubdivisionPreserver` lifts actual base walks and
proves full connectivity preservation for arbitrary added core edges. It allows
branch vertices to be isolated whenever they are also isolated in the input
and does not assume the post-fault certificate is globally connected.
`CycleCertificate` specializes to the native cycle graph and proves the actual
(2f−1)-fault certificate and exact vertex count. `SubdivisionWeight` gives an
explicit dart encoding and unit-weight upper budget. `CycleLinearization`
proves the cut cycle lies in the ordinary path graph. `PotentialForcing`
telescopes a real potential along actual walks and forces retention from an
explicit fault-set potential witness.

These statements do not yet include the constructed heavy-edge potential,
rotation to all core edges, genuine optimal-denominator lower ratio, or the
joined quantitative Theorems 9–10. No new main lower bound is claimed.
Local aggregate/axiom/kernel gates and review results are recorded below when
completed; this source update alone is not evidence that those gates passed.

29-module local build/root/index: PASS with all new-source warnings treated as errors. All 284 project declarations pass the exhaustive allowed-axiom audit. All eight new exact-source independent kernel replays passed in two bounded groups. Independent semantic/source review returned PASS; its frozen report is recorded in SIXTH_SEMANTIC_REVIEW.md. This is a component review, not a final whole-paper audit. Exact-commit CI for the new 29-module checkpoint will run after publication.
