# Counterfamily and graph foundations — 10 October 2026

Status: partial proof checkpoint, not a main-result completion.

## Current expanded scope

Twelve modules and their aggregate root compile locally. All 151 declarations,
including generated/private declarations attributed to these modules, pass the
allowed-axiom audit (propext, Classical.choice, Quot.sound only). Module index
passes. The exact eight new source hashes pass an independent semantic review,
recorded in SECOND_SEMANTIC_REVIEW.md and SECOND_SOURCE_HASHES.json.

The actual graph counterfamily is formalized: for every m≥3, a true positive
minimum two-fault denominator exists, and every one-fault stretch-5/2 spanner
of unit K_(m,m) has competitive lightness ≥m/6. At m≥4 the true three-fault
denominator yields ≥m/8. The proof constructs actual hub certificates, proves
connectivity after every allowed fault set, and bounds their edge weights by
6m or 8m. It does not assume a denominator or final inequality. The extremal
lambda supremum and the asymptotic contradiction are not yet encoded in these
modules; their exact source-level argument is independently reviewed in
LAMBDA_COUNTERFAMILY_AUDIT.md.

Other new components are literal ENNReal metric semantics, missing-edge
connectivity/degree, the actual greedy blocking invariant (Lemma20), finite
host counting and conditional baseline algebra, and the MST cycle-maximum
exchange fact. Host-forest existence and full sampled graph pruning remain open.

## Gates

- Local build/root: PASS (12 modules).
- Exhaustive allowed-axiom audit: PASS (151 declarations).
- Module index: PASS.
- Independent semantic review of the eight added sources: PASS.
- Separate new-module kernel replays: PASS (all eight new modules). Earlier four unchanged modules had already passed replay.
- Exact-commit CI for this expanded checkpoint: pending publication.
- Fresh whole-paper skeptical final audit: not requested; main scope incomplete.

## Earlier checkpoint

Exact commit aedcf714c75ad2db7ee81ae3d0dc56e279155659 passed full CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38075342370 .
This includes build, all repository module indexes, all-declaration axiom audit
and every project module's independent kernel replay. Its four-module semantic
review is INITIAL_SEMANTIC_REVIEW.md. Those earlier checks do not imply the
expanded checkpoint's exact-commit CI passed.

Main upper/lower/runtime theorems, Eulerian Steiner-forest packing, actual
graph-weight sampling assembly and the multigraph extension remain open.
