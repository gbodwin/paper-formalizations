# Actual lower-family checkpoint — 10 October 2026

Status: active partial verification. Main upper/lower/runtime scope is incomplete.

## Exact CI-green reviewed baseline

Commit `cff07e88f8e16711368e3cd55c6ae658f3dfcc2b` contains36 modules and369
project declarations, including the actual real-stretch lower family. All
local gates, exact-source kernel replays, and frozen independent reviews pass.
Full exact-commit CI passed at20:56:59 UTC, including repository-wide replay:
https://github.com/gbodwin/paper-formalizations/actions/runs/38084671078 .

The preceding commit `30ff80ef6bf429d823bf14d84866f4ac1b996fe6` contains 21 modules and 229
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


## Actual Section 4.1 finite lower family

Seven new frozen modules are recorded in SEVENTH_SOURCE_HASHES.json. All sources
compile with warnings treated as errors. The complete 36-module/root/index gate
passed, and all 369 project declarations have only propext, Classical.choice and
Quot.sound as axioms. All seven new exact-source kernel replays passed in two bounded groups.
Independent source/semantic review returned PASS, recorded in
SEVENTH_SEMANTIC_REVIEW.md. Its note that four replays were pending was accurate
at review time; seventh-replays-b.log records their subsequent PASS. No
whole-paper final audit is implied.

The explicit graph is the f-colored subdivision of the native cycle of length
M=m+3, with a heavy direct edge on each base-cycle edge. Every eligible output
retains every heavy edge, by actual fault sets and a telescoping rotated
potential. The unit-edge graph is a genuine q-fault certificate for q≤2f−1.
The denominator is the actual positive minimum preserver weight. Thus the
integer-stretch family has ratio at least n/(8 f² k), and the arbitrary-real
stretch t≥1 version has ratio at least n/(16 f² t). The admissible finite range
is m+2≥2 ceil(t), with n=(m+3)(f+1). The input itself is an eligible spanner;
there are admissible graphs of arbitrarily large order for fixed parameters.

This supplies the mathematical lower-family scope used by Theorem 9. It does
not establish a literal every-n, epsilon-independent reading of Theorem 10's
lower display. Exact source conventions and this distinction are included in
the bounded review. Theorem 10's upper half and Theorem 34 remain open.

The new 36-module exact-commit CI starts after publication. The prior 29-module
commit 9aa8ae3c5166dc4d348a3dbc1431bc4bef0e6ddd has passed CI build, index and
axiom stages; its repository-wide kernel replay is still running at 20:36 UTC:
https://github.com/gbodwin/paper-formalizations/actions/runs/38082449507 .


## CI runtime-budget follow-up

The 29-module run 38082449507 reached the configured 30-minute job ceiling and
was cancelled at 20:36:59 UTC, after its build/index/axiom stages passed. Its
log shows steady sequential replay progress with no reported kernel failure;
the last announced module was SubdivisionCleanColor, whose completion must not
be inferred from that start line. Therefore this run is not a full CI PASS.

The 36-module source/semantic checkpoint was pushed as
242611f0ded9e5eace12e5e705b6a6a638697a2a, with run 38084590994. A follow-up raises
the CI job budget from 30 to 60 minutes while preserving every build, audit,
index and sequential kernel check. The exact follow-up head must pass its own
CI before it is called fully CI-green. No local proof source changed.


## Supplied spanning-packing assembly

Three further frozen sources are listed in EIGHTH_SOURCE_HASHES.json. All39
modules/root/index compile, all377 project declarations pass the allowed-axiom
audit, and the three new exact-source official kernel replays pass. Independent
component review returned PASS in EIGHTH_SEMANTIC_REVIEW.md.

The actual assignment filter derives coverage and blocker avoidance from the
supplied tree count and actual congestion. Incidence counting retains the
seed baseline1. The joined theorem uses the actual recursive output and its
actual constructed blocking map, with the denominator a genuine optimum seed;
its positivity is proved from a supplied tree. The exported ratio is
1+8fL/h, where L=8+2048/epsilon*n^(1/k).

The supplied trees all span one common vertex type, lie in the optimum seed,
number at least2f+h, and have congestion at most2. Their existence is not proved.
General subtree transport, the global Eulerian forest packing and optimized
upper assembly remain open. This is a conditional component checkpoint.

The proof-identical36-module timeout-recovery head is
cff07e88f8e16711368e3cd55c6ae658f3dfcc2b. Its exact CI38084671078 passed all stages, including repository-wide kernel
replay, verified20:56:59 UTC. The newest39-module exact CI starts after
publication. The36-modulecff07e8 checkpoint is the latest fully CI-green baseline.

## Actual induced-host transport

Three new frozen sources are recorded in NINTH_SOURCE_HASHES.json. All42
modules/root/index compile; all398 project declarations pass the allowed-axiom
audit. Allthree exact-source official kernel replays passed. Independent bounded
source/semantic review returned PASS, recorded in NINTH_SEMANTIC_REVIEW.md.
These component gates do not establish a fresh whole-paper final audit.

The new theorems restrict actual blocking data along injective vertex maps,
transport actual unordered-edge sums and total graph weights exactly, and
apply the proved sampling/pruning argument on each genuine local tree domain.
The global-order bound follows from the actual cardinality injection. Empty
candidate sets and singleton hosts are handled, rather than excluded by a
hidden size assumption. Positive weights are required only on actual global
input edges; f,k are positive naturals and epsilon is positive.

This is a per-host transport result. The dependent-family assignment/incidence
join and forest-packing existence remain open. No unrestricted main upper
bound or fresh whole-paper final audit is claimed.
