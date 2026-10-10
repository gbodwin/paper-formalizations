# Pruning, weighted sampling and counterfamily growth — 10 October 2026

Status: partial proof checkpoint, not a main-result completion.

## Current expanded scope

Sixteen modules and their aggregate root compile locally. All 171 declarations,
including generated/private declarations attributed to these modules, pass the
allowed-axiom audit (propext, Classical.choice, Quot.sound only). Module index
passes. The earlier eight-module addition passed an independent semantic review,
recorded in SECOND_SEMANTIC_REVIEW.md and SECOND_SOURCE_HASHES.json. The
latest four modules have not yet had their independent semantic review; it is
queued after other projects in the shared reviewer slot.

The actual graph counterfamily is formalized: for every m≥3, a true positive
minimum two-fault denominator exists, and every one-fault stretch-5/2 spanner
of unit K_(m,m) has competitive lightness ≥m/6. At m≥4 the true three-fault
denominator yields ≥m/8. The proof constructs actual hub certificates, proves
connectivity after every allowed fault set, and bounds their edge weights by
6m or 8m. It does not assume a denominator or final inequality. CounterfamilyGrowth additionally proves that no constant C times sqrt(2m)
bounds either of these two ratios, on the same family with both true optima.
The extremal lambda supremum itself is not encoded; the source-level lambda
comparison remains independently reviewed in LAMBDA_COUNTERFAMILY_AUDIT.md.

Other new components are literal ENNReal metric semantics, missing-edge
connectivity/degree, the actual greedy blocking invariant (Lemma20), finite
host counting and conditional baseline algebra, and the MST cycle-maximum
exchange fact. GraphPruning now constructs the actual blocker-deleted and MST-pruned graph
on a spanning host vertex set, proves its girth, and constructs a retained MST
no heavier than the host tree. WeightedSampling proves the finite expected
non-seed weight and supplies an actual sample witness. StretchParameters proves
the corrected threshold gap and actual coarse graph-lightness bound. The host
packing and vertex-set transport remain open; the separate graph sampling
components have not yet been fully assembled into a main upper theorem.

## Gates

- Local build/root: PASS (16 modules).
- Exhaustive allowed-axiom audit: PASS (171 declarations).
- Module index: PASS.
- Independent semantic reviews: PASS for the first 12 modules; latest four queued.
- Separate new-module kernel replays: PASS (all four latest modules). Earlier twelve unchanged modules had already passed replay.
- Exact-commit CI for this expanded checkpoint: pending publication.
- Fresh whole-paper skeptical final audit: not requested; main scope incomplete.

## Earlier checkpoints

The 12-module checkpoint e79a8b06353ed2155bca7080080724c5abfba193 passed
local build/index/audit of151 declarations,
all module replays and independent semantic review. Its exact CI has completed
build/index/axiom audit and was still replaying repository modules at18:53:
https://github.com/gbodwin/paper-formalizations/actions/runs/38076966078 .


Exact commit aedcf714c75ad2db7ee81ae3d0dc56e279155659 passed full CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38075342370 .
This includes build, all repository module indexes, all-declaration axiom audit
and every project module's independent kernel replay. Its four-module semantic
review is INITIAL_SEMANTIC_REVIEW.md. Those earlier checks do not imply the
expanded checkpoint's exact-commit CI passed.

Main upper/lower/runtime theorems, Eulerian Steiner-forest packing, actual
graph-weight sampling assembly and the multigraph extension remain open.
