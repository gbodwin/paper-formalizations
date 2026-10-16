# ExecutableVotingWork three-recursor pilot

Tested source: `9836cc5c9f529fa217a56dea19aea8be8f397ded`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

The bounded sampleWork/hostWork/edgesWork repair is validated incrementally. Exactly their three partial companions are removed, with none added: **55 → 52**. The unchanged strict complete-owner gate still fails. No CI is started. Independent review is pending before any further definition is repaired. Theorem 34 and whole-paper completion remain open.

## Accepted baseline and qualifications

The parent reports independent acceptance of source `05d0ab325ee7b4e1dd7fc84713f2676a7f311936` and evidence `a2d3369f7acbd0b8f84a6019ed43d02a5af58447`, including all manifest entries, audit chunks and 501 persisted-preflight receipts. This records source/log/hash reconciliation, not new reviewer execution. That pilot was incremental fresh-output validation using pinned dependency caches and recorded byte-identical import hashes. A **clean final exact-source gate is still required**.

This pilot also uses incremental validation. Its isolated `.lake/work-pilot/lib/lean` directory began with 486 byte-verified copies bound to the accepted source/object ledger. The changed leaf and aggregate were strictly rebuilt; the other **484 objects are inherited**, with unchanged source and immediate-import hashes. `source-object-provenance.json` distinguishes every new compilation from every inherited object. These inherited objects are not claimed as new compiler executions. The audit itself is fresh and complete against the resulting isolated object set. No old project directory is used as a fallback on the audit search path.

Historical qualifications remain: the Controller pilot retained 494 persisted preflights for 495 receipts, and the older aggregate-prefix OOM violated the sequencing requirement through internal replay tasks. Neither is rehabilitated here. All prior 3,242 edges-pilot, 2,725 Controller-pilot and 5,161 strict-aggregate manifest entries were rehashed unchanged.

## Exact source and semantics

Only `ExecutableVotingWork.lean` changes among the 486 closure sources. `sampleWork`, `hostWork` and `edgesWork` use explicit total `List.rec`, retaining their original argument/result types. The entire pair is preserved, including the work counter. Six explicit nil/cons equations are proved by `rfl`. All nine existing theorem statements are byte-identical, including the value, cost, measured-run and assignment-run statements; supporting proofs use the explicit equations.

`LegacyEquivalence.lean` imports the preserved old implementation and defines the three replacement bodies byte-identically in a comparison namespace. It proves each entire output pair equal to the old function for every input. The host proof uses the sample full-pair equality, and the edges proof uses the host full-pair equality. The old source snapshot and all 486 old object hashes are checked before compilation. All three equality proofs pass strict compilation and report only `propext`, `Classical.choice` and `Quot.sound`. This is stronger than checking the value projection alone.

`PilotCheck.lean` verifies that all three definitions are safe, nonpartial, computable, use List.rec, have no self-reference and have no partial companion. Thirteen executable full-pair fixtures pass: empty samples, uncovered and covered samples, repeated samples; empty, ineligible, empty-tape and admitting hosts, repeated hosts; empty edges, admission, rejection and repeated edges. Counter values are checked explicitly, not merely output cardinalities.

The existing unit-cost work interpretation and all input hypotheses remain unchanged. No physical runtime, bit-cost, seed/host/order construction or random-generation claim is added. No blanket noncomputable change, unsafe shim, warning suppression, generated-name filtering or extra axiom is introduced.

## Fresh audit and singleton replay

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine pinned dependencies are unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. New strict compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. Both module and aggregate compilations pass with zero warning headers.

The complete owner audit and resolver are byte-identical to the accepted versions except their output paths. Every owner is inventoried; recursive types/bodies, opaque values, inductive families and recursor rules are traversed. The fresh result is **9,285 roots, 60,704 recursive constants and 48 opaque bodies**. Only the standard three axioms occur. There are no unsafe project roots and no aggregate-owned declarations.

The exact removed partial names are:

- `LightEFTSpanners.ExecutableVoting.sampleWork._unsafe_rec`
- `LightEFTSpanners.ExecutableVoting.hostWork._unsafe_rec`
- `LightEFTSpanners.ExecutableVoting.edgesWork._unsafe_rec`

The other 52 partial names are unchanged. The strict audit returns exit 1 with **104 findings**, one root and one recursive finding per remaining partial. This is not a passing gate. Full diagnostics and remaining names are retained without exclusion.

The full name delta removes 32 roots and adds seven, all owned by ExecutableVotingWork: the six equation theorems and a replacement generated simp helper are added. Removed helpers include the lazily generated `ExecutableVoting.edges.eq_1`, whose actual owner was ExecutableVotingWork; using the already-proved explicit `edges_cons` no longer generates it there. The accepted edges definition/source is unchanged. The complete delta is preserved rather than inferred from name prefixes.

The official target resolver reports exactly one module/object for `LightEFTSpanners.ExecutableVotingWork`. The supervisor repeats the filesystem resolution under the common exclusive lock. The official `leanchecker -v LightEFTSpanners.ExecutableVotingWork` passes with exactly one replay line. `LEAN_SYSROOT` names the official toolchain. No aggregate-prefix replay or parallel worker is used.

## Execution evidence and review

Seven fresh UUID receipts cover one legacy comparison, two strict project compilations, one executable/metadata check, one complete audit, one official target-resolution check and one singleton replay. Every invocation has a persisted process/resource preflight bound by UUID and hash, submitted-source snapshots/hashes, full argv, lock inode, child PID, UTC/monotonic times and reaping. Reconciliation verifies non-overlap and child reaping. There were no development compilation failures; the expected strict-audit rejection is the sole nonzero attempt, with its raw diagnostics retained. Successful checks have zero warning headers. Hints and option names are not counted as warnings.

`reconcile.py` checks sources, objects, direct imports, new-versus-inherited provenance, complete recursive closure, exact companion delta, actual-owner changes, singleton resolution, all receipt/preflight hashes and preservation. The complete TSV is also exported into 208 ordered row-aligned chunks; `audit-export/manifest.json` contains per-chunk and reconstruction hashes. Concatenate bytes in listed order without separators or repeated headers.

Entry points are `legacy_compare.py`, then sequential `run.py pilot`, `run.py build`, `run.py audit` (expected exit 1), and `run.py replay`. Read-only reconciliation does not run Lean. No default Lake build, dependency update, website change, other-project proof work or automatic CI is used. Publication is additive with `[skip ci]`; the worker stops for independent review.
