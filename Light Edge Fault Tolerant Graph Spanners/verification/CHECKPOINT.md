# Lower-certificate obstruction checkpoint — 10 October 2026

Status: active partial verification. Main upper/lower/runtime scope is incomplete.

## Exact CI-green reviewed baseline

Commit `827800bb20f1b59b896be0a0a1a5f5294f6dc788` contains 16 modules and 171
project declarations. Its local root/index/build, exhaustive allowed-axiom audit
and all module kernel replays passed. Independent semantic review now covers
all sixteen modules; the newest four are reviewed in
`FOURTH_SOURCE_AND_COMPONENT_AUDIT.md` against `THIRD_SOURCE_HASHES.json`.
Full exact-commit CI passed, including repository-wide kernel replay:
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
Expanded exact-commit CI: not yet published.

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
complete sampled-graph weight assembly; optimized heavy/light sampling; a valid
replacement lower-bound certificate/construction; other lower bounds; randomized
conditioning/concentration and runtime; the source multigraph extension.

A supplied host tree is a genuine premise of the current pruning theorem.
WeightedSampling alone does not handle deterministic host-tree blockers; the
assembly must explicitly prove those blockers avoid the host. The component
results do not imply a main theorem until these obligations are discharged.

No fresh whole-paper skeptical final audit has been requested, and no public
research-site link is implied by this partial checkpoint.
