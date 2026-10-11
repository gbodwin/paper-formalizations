# Actual lower-family checkpoint — 10 October 2026

Status: active partial verification. Main upper/lower/runtime scope is incomplete.

## Latest status (23:51 UTC)

The full-CI and independently reviewed proof baseline is72 modules/577
declarations at117130f1621f40a39749d0dc27145cdb4f2d4a71. Exact CI38095126415
passed all stages, including every repository kernel replay, at23:42:21:
https://github.com/gbodwin/paper-formalizations/actions/runs/38095126415 .
The matching review is FIFTEENTH_SEMANTIC_REVIEW.md atf8ed484cb46e01e6d71262ae804310eb228c11a0;
that report commit has its separate CI38095501137, still running.

The new78-module/631-declaration checkpoint has all six strict production builds,
root/index, allowed-axiom audit and six official kernel replays passed locally.
Earlier72 proofs and objects were reused unchanged. Fresh six-file semantic review returned component PASS at00:06 UTC on11 October; a full clean exact78 CI has not yet passed. The new packet proves
actual native partition refinement, explicit termination, conditional local
exchange transport and forest-density facts. General packing existence, splitting
and the paper's full upper/lower/runtime scope remain incomplete.

## Historical CI-green checkpoints

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

## Heterogeneous supplied-subtree assembly

The next three exact sources are frozen in TENTH_SOURCE_HASHES.json. Their
strict source checks and complete45-module/root/index gate pass. All403
project declarations pass the allowed-axiom audit. Allthree exact-source official kernel replays pass. Bounded independent
semantic review returned PASS in TENTH_SEMANTIC_REVIEW.md. This does not certify any unrestricted main upper theorem.

The actual family uses finite vertex types A i and injective maps into the
original graph, with genuine trees T i on those local domains. No common
spanning vertex set or hidden minimum host size is required. A concrete
pullback/filter assignment and a restricted-index union bound derive at least
h unblocked host votes from 2f+h actual joint-endpoint hosts and congestion two.
Exact weighted incidence, including finite-enumeration normalization, yields
1+8fL/h. The actual optimum-seeded output has that bound and the EFT guarantee.
The zero-denominator case follows the existing total division convention and
is explicit; no positive-denominator claim is made for that case.

The structural packing is supplied, not constructed, and its relationship to
q remains open. Eulerian forest packing, the multigraph extension, optimized
heavy/light sampling, a Theorem34 replacement certificate and runtime remain
substantive remaining obligations.

The prior39-module exact commit81a15b8a18f50768f1eb9c8f9f4be5e0dd7902dd passed
full CI38085816118 at21:20:41 UTC, verified with matching head and all job steps.
The42-module transport head3b542ca23bd80620686efe453ed7b39e6a02fdf3 has its own
run38087103105 pending at this record's preparation; local and semantic gates
are not a substitute for that exact-commit result.

## Native forest components and exact real-eta competition

Four exact sources are frozen in ELEVENTH_SOURCE_HASHES.json. Complete49-module
strict source/root/index and all428 declarations' allowed-axiom audit pass.
All four exact-source official kernel replays pass. The independent bounded
semantic review in ELEVENTH_SEMANTIC_REVIEW.md returned PASS after verifying
the frozen hashes and actual graph semantics. None of these gates constitutes
the fresh final whole-paper audit.

Native connected components provide the actual varying tree domains. Projection
of a fixed edge's component-host indices to forest indices is injective, so its
congestion cannot increase. Each forest connecting two actual endpoints supplies
its canonical component as a genuine host. The seeded-output join uses proved
native(q+1)-edge connectivity for each missing input edge of a q-fault preserver.
It still requires supplied acyclic subgraphs preserving these pairs, enough
forest indices, congestion two and q+1≥2f+h. Their existence remains open.

The separate rounded wrapper uses the actual real budget floor((2+eta)f), proves
its exact decomposition2f+floor(eta f), and derives the uniform finite coarse
bound1+8L/eta from votes floor(eta f)+1. Here L=8+2048/epsilon*n^(1/k), eta>0,
and the supplied subtree packing is explicit. Baseline1 is retained with no
upper restriction on eta. This does not prove a printed lambda comparison or
the optimized heavy/light upper bound. All zero-denominator handling remains
explicit through the existing ratio convention.

The prior 42-module and 45-module exact heads both passed full CI, verified
2026-10-10 at 21:50 UTC: runs 38087103105 and 38088236308 respectively.
The latest full-CI baseline is 45 modules at
36c403565bb2c911408b368df0979acc417100ee. This new 49-module checkpoint
requires its own exact-commit CI after publication.

## Actual simple-subdivision doubling and projection

Seven new sources are frozen in TWELFTH_SOURCE_HASHES.json. Their strict
source builds, the 56-module root/index gate and all 470 declarations'
allowed-axiom audit passed at 22:11:15 UTC on 2026-10-10. The local gate used
unchanged prior module objects rather than rebuilding all 56 sources. Official
new-module kernel replay and independent semantic review are separate gates.

Actual selected-color half-edge faults project injectively to original edges.
Native core edge-connectivity is multiplied by the copy count. With two copies,
all actual degrees are even; branch vertices have degree two and cannot belong
to a nontrivial connectivity island of threshold at least three.

Complete two-half-edge paths, rather than dangling branches, define the core
projection. Actual core walks project with stationary reversals allowed. Native
spanning forests are constructed without losing reachability. Each original-edge
host is charged to a distinct copy through an actual half-edge, so edge-disjoint
subdivision subgraphs yield congestion at most two. The same optimum-seeded
output then satisfies the earlier finite coarse ratio bound, under an explicit
supplied edge-disjoint connectivity-preserving subdivision family.

This discharges the simple doubling/projection interface, not the external
forest-packing existence theorem. No connected Euler-tour claim is made for
disconnected input, and no multigraph main-upper extension is inferred.
Separately, positive actual input-edge weights make any true preserver weight
positive whenever the input is non-edgeless. Thus the explicit zero-denominator
case occurs exactly for an edgeless input under those hypotheses.

All seven official new-module kernel replays now pass in two bounded groups,
completed at 22:13:57 and 22:15:26 UTC. Exact hashes remain frozen. The
independent seven-file component semantic review returned PASS at 22:29:26 UTC,
recorded in TWELFTH_SEMANTIC_REVIEW.md. It independently matched production
hashes and Git blobs and checked the actual graph semantics and degenerate
domains. No final whole-paper audit or unconditional upper theorem is implied.


## Actual cut and contracted-core foundations (newer packet)

Eight exact sources are frozen in THIRTEENTH_SOURCE_HASHES.json. Their individual
strict diagnostics pass. All eight new production sources, the 64-module
root/index and the exhaustive 530-declaration allowed-axiom audit passed at
22:49:48 UTC. The local gate reused unchanged earlier objects; it did not
freshly rebuild every previous source. The first four official new-module replays passed at
22:51:47 UTC. That window also strictly rebuilt a documentation-only precision
change in the parallel-edge example (equal endpoints use reflexive reachability).
The final four replays passed at22:52:59 UTC. The independent eight-file
semantic review returned component PASS at22:57 UTC, recorded in
THIRTEENTH_SEMANTIC_REVIEW.md. Exact64-module CI remains running.

The packet uses actual finite cuts, native graph edge identities through
contraction, and genuine surviving walks after deleting original edge IDs.
It constructs a minimal deficient core from native basic-instance hypotheses,
proves its contracted fault connectivity, and derives the actual crossing-edge
partition criterion. Parallel edges and loops are counted correctly; simplifying
adjacency occurs only after a specified deletion. The final partition wrapper
explicitly uses nontrivial surjective partitions. A singleton partition has
zero required crossing edges. Packing existence is still unproved.


## Integral general-multigraph core extension (newer packet)

Four frozen sources are listed in FOURTEENTH_SOURCE_HASHES.json. All four strict
production builds,68-module root/index and exhaustive548-declaration allowed-
axiom audit passed at23:06:32 UTC. The four exact official kernel replays passed
at23:07:54. Earlier objects were reused unchanged; this local gate is not a
fresh full68 rebuild. Independent four-file semantic review returned component PASS at23:21:37,
recorded in FOURTEENTH_SEMANTIC_REVIEW.md. It matched all four published hashes
and all64 prior proof sources. Published c3a3aae006f140cfb1b007974320f0d3b3ea90d6
has exact CI38094267232 running; the review-report commit has its own separate CI.

These sources extend integral minimal-core selection and the genuine contracted
fault-connectivity/partition-budget join to native finite multigraph inputs.
Basicness and retained core membership use the actual vertex set. Parallel
identities remain distinct. The full-vertex condition is explicit before
interpreting a finite ambient-type cardinality decrease as a graph-order
statement. The weighted fractional source lemma and packing/splitting/expansion
existence remain open; no main upper bound is completed by this extension.

The proof-identical reviewed 56-module report commit26f58f279857575e28088bc92605dd01bd70ea49 also passed its own complete exact CI38091887677 at23:05:46 UTC, including all repository kernel replays. This is separate from the pending64/68 statuses.


## Full exact64 CI and newer native forest packet

Both64-module exact runs have now passed every step, including all repository
kernel replays: reviewed report15f6e7cfae93c49cb836c6b91f543b9c1ea9c09f,
CI38093343350 completed23:21:09; proof9752254f87cad1849129b264b8ee2cd08fcc9afc,
CI38093142749 completed23:23:00. Both heads, terminal states and steps were read
back23:26. Thus64 modules/530 declarations is the full-CI reviewed baseline.
Reviewed68 own exact CI remains pending.

Four new source hashes are frozen in FIFTEENTH_SOURCE_HASHES.json. All four
strict production builds,72-module root/index and exhaustive577-declaration
allowed-axiom audit passed23:24:22. All four official kernel replays passed
23:27:08. Previous68 proof sources and their objects were reused unchanged;
this is not a clean full72 local rebuild. Fresh four-file semantic review returned component PASS at23:33:43, recorded
in FIFTEENTH_SEMANTIC_REVIEW.md. It independently matched all four frozen and
published117130f source hashes and all68 prior proofs. Exact72 CI38095126415
is still running; the review-report commit has its own separate CI. No whole-paper final audit or completion claim is implied.

The new construction selects actual original identities, preserves all actual
vertices and exact reachability, proves every retained edge a native bridge,
and constructs a spanning tree with its exact count when input is connected.
The final finite connected-edge lower bound assumes finite actual vertex and
edge sets. General tree packing, Eulerian forest packing, splitting and expansion
remain open. The external weighted fractional core theorem is still outside scope.


## Full exact72 CI and newer finite packing foundations

Exact proof checkpoint117130f1621f40a39749d0dc27145cdb4f2d4a71 passed full
CI38095126415 at23:42:21, including all repository kernel replays. Run head,
terminal result and every step were independently read back23:44. Its semantic
review report is recorded atf8ed484cb46e01e6d71262ae804310eb228c11a0, whose own
CI38095501137 remains separate and pending. The68 proof checkpointc3a3aae also
passed full CI38094267232 at23:42:14. The full-CI reviewed baseline is now72
modules/577 declarations, without any whole-paper completion claim.

Six exact new sources are frozen in SIXTEENTH_SOURCE_HASHES.json. All six strict
production builds,78-module root/index and exhaustive631-declaration axiom audit
passed in two bounded windows, completed23:42:13 and23:43:58. The first three
official replays passed23:45:02; the last three passed23:50:37. Earlier72 proofs
and their objects were reused unchanged, not freshly rebuilt by this local gate.
Fresh six-file semantic review is queued after the allocated minor-free review
and Flow constructor helper. Future exact78 CI is a separate pending gate.

The new scope is actual partition crossing/one-tree sufficiency, true component
refinement with least-color priority and an explicit n² termination bound,
conditional local edge-exchange walk substitution, and actual forest-density
nonbridge forcing. The replacement route is explicitly supplied in the local
exchange helper, not assumed to exist for the full packing construction. The
source's general packing/maximality contradiction and finite-level cycle selection
are still open, as are Mader splitting, forest expansion and full main upper bounds.

## Frozen78 semantic review (11 October,00:06 UTC)

The fresh six-file source/semantic review returned component PASS and is recorded
in SIXTEENTH_SEMANTIC_REVIEW.md. It matched all frozen and published9b2a722 source
hashes, all72 prior proof bytes, the exact78-module index and all recorded gates.
No semantic blocker was found. The exchange route remains an explicit premise,
and the density theorem produces a native nonbridge rather than a complete
crossing-cycle/exchange construction. General packing and full main scope remain open.
Exact78 proof CI38096551852 is running; a report commit has a separate exact run.

The reviewed72 report commitf8ed484 also passed full CI38095501137 at00:01:30,
with all steps read back00:04. Its full72 clean build and every repository kernel
replay passed. Thus both the72 proof and report checkpoints are fully green.

## Actual terminal quotient packet (11 October,00:09 UTC)

Seven new sources are frozen in SEVENTEENTH_SOURCE_HASHES.json; all78 earlier
proof files are unchanged from reviewed1d33c9e705ad48570d4f9787b5e19e8a7a1c475c.
All seven strict production builds passed in two bounded groups, and the85-module
root/index plus exhaustive667-declaration allowed-axiom audit passed00:09:34.
Prior78 objects were reused unchanged; this is not a clean full85 local rebuild.
All seven official kernel replays passed in two bounded groups, at00:10:57 and00:12:37. The fresh seven-file semantic review returned component PASS at00:17:30 (SEVENTEENTH_SEMANTIC_REVIEW.md).

The packet proves the native induced-core partition premise, contraction of
actual native forests along genuinely connected fibers, exact quotient-tree
counts, original-walk lifting, exact colored crossing-identity accounting and
the last-color terminal density/alternate-path obstruction. Actual vertex images,
finite target domains and explicit connected-fiber hypotheses are preserved.
The source's minimum-level exchange and maximality contradiction remain open,
as do general packing, splitting, Steiner forests, expansion and main bounds.

## Frozen85 semantic review (11 October,00:17:30 UTC)

The independent seven-file source/semantic review returned component PASS with
no blocker. It verified exact frozen/checkpoint9c2e5d1 hashes, prior78 proof byte
equality, the exact85-module index and all recorded gates. The terminal theorem
returns an actual last-color crossing identity and same-color reachability after
deleting that same identity. First-color trees, genuine connected fibers and
surjective labels remain explicit induction-step premises. Label construction
from terminal iterates, minimum-level selection, exchange/maximality and full
packing are not claimed by this85 packet. Exact proof CI38097692047 is running,
separately from any report-commit run; full reviewed72 CI remains the baseline.

## Full78 CI and next finite-level packet (11 October,00:30 UTC)

Exact78 proof CI38096551852 at9b2a722589b4484ccacb897f0357be1dd07cc3b2
completed successfully00:23:23. Head, terminal state and every step including
clean build and repository-wide kernel replay were read back00:25. The fresh
six-file semantic report is published at1d33c9e705ad48570d4f9787b5e19e8a7a1c475c,
whose own exactCI38097331985 remains pending. Full-CI reviewed baseline:78/631.
Reviewed85 proof9c2e5d1 and report33803cb have separate CIs running.

Six new sources are frozen in EIGHTEENTH_SOURCE_HASHES.json. Strict production
builds passed in two bounded windows,00:26:44 and00:28:22. The91-module root/index
and exhaustive704-declaration allowed-axiom audit pass. Prior85 sources and
objects remain unchanged and were reused; no clean full91 local rebuild.
All six official kernel replays passed in two bounded groups, by00:34:17 and00:35:24. Fresh six-file semantic review and exact91 CI remain pending.

The packet constructs finite occupied-block labels and real terminal fiber
connectivity, selects a minimum finite-level native nonbridge, and constructs
an alternate same-color route inside its level using cut symmetric difference.
The joined source countercase no longer takes labels, fiber connectivity, a
minimum edge or replacement path as input. The exact least splitting color is
also shown to be an earlier color. Initial first-color trees and last-color
disconnection remain the explicit inductive countercase. Full exchange,
maximality contradiction, packing, splitting, expansion and main bounds remain open.

## Independent91 component review (11 October,00:40 UTC)

Proof472def1a65d2a35113a21739955cf8285c20a6fc, tree4d47500dc99d0e0a7e818281331c24ed10d3362f, was published and read back00:36. Exact CI38099004674 is running. The fresh six-file review returned COMPONENT PASS00:40:40; see EIGHTEENTH_SEMANTIC_REVIEW.md. It independently verified current/frozen/published source hashes, prior85 proof equality and the exact91 root/module index. No new proof-source blocker or correction was found. The inherited HostCounting statement-map omission and stale replay note were corrected after review, without changing any Lean source. All91 modules are now represented in the human statement map.

The78 report commit1d33c9e exact CI38097331985 also passed fully at00:34:56; head and every job step were read back00:40. Thus both78 proof and report commits are fully CI-green. Local gates, component semantic review and exact full CI remain distinct. Tree exchange/maximality and the main forest-packing/splitting prerequisites remain open in the91 scope.
