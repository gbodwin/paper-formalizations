# StoredWeightLookup.value total-recursor pilot

Tested source: `87a70c27a49e920349b53e31c9f96689bc237fb6`. Branch: `light-eft-spanners-checkpoints`. Source/object binding is recorded in `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredWeightLookup.value._unsafe_rec` disappears: **33 → 32 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **64 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and additive correction

The parent independently accepted source `60824d24211dee4a7437f226910c9232950606c4` and evidence `737669761cf979f54aa449acceb4501e8dbfb15f`. Review had finished before work began. This records source/log/hash reconciliation, not fresh reviewer execution or live-object inspection.

Precision correction to that historical rowValue report: its initial free disk was **18.05 GiB** and terminal free disk **17.97 GiB**, rather than approximately 19 GiB. This correction is additive; the historical report, raw observations, manifest and evidence remain unchanged.

The environment connection was live, HEAD and tracked state matched the accepted evidence, all 1,428 parent-manifest entries and all 486 live source/object bindings verified. No Lean/Lake/checker was active and the common lock was free. The actual value declaration was inspected before replacement. Current resource bytes and UTC observations are retained in initial-observation.json and terminal-observation.json; disk is reported in GiB using 2^30 bytes. No canceled workspace or other paper was accessed.

## Exact semantics and source scope

The replacement uses total List.rec over the outer matrix, producing a function of the row index. The column index is fixed throughout the traversal. Empty matrices yield zero, row index zero delegates to unchanged rowValue at the requested column, and a successor row index uses the tail at its predecessor. Three explicit equations are proved by rfl.

LegacyEquivalence.lean imports hash-bound accepted objects and proves equality of the complete rational result for every natural i,j and arbitrary list of rational lists. It inducts over the outer list, generalizing i and splitting the legacy empty-list index case. The replacement body is identical to production. The successful theorem uses only propext and Quot.sound, adding no mathematical premise. There is no rectangularity, nonempty-row, in-range, nonnegativity or matrix-validity restriction.

Twenty fixtures compare the entire rational result, covering empty matrices, empty selected rows followed by nonempty rows, unequal row lengths, all positions of signed fractional data, out-of-range row and column indices, huge independent indices, zero payloads, repeated values, large fractions and longer matrices. Universal equation examples and metadata checks verify safety, totality, computability, explicit List.rec, no self-reference and no partial companion. Selecting an empty row returns zero without searching subsequent rows.

Only value changes definition. Everything before it remains byte-identical, including repaired rowValue, its equations, State and transition. rowSteps and steps remain byte-identical. All ten pre-existing theorem statements preserve their hypotheses. Four proof simplification arguments in lookup_trace and value_eq use the explicit equations; these were adjusted before compilation based on the accepted analogous repairs. All other existing proof bodies are unchanged. All other 485 closure source files remain unchanged. Semantic equality is not a claim about physical runtime or recursor evaluation cost.

## Sequential validation

The independently rederived source-import closure contains 131 affected modules and 355 unaffected modules. Every affected module, including aggregate compilation, receives a fresh strict build; affected state entries were removed before rebuilding so intermediate object equality cannot skip required compilation. The 355 inherited objects retain accepted source, direct-import and object hashes. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all nine revisions; exact manifest, executable and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, alternate runtime, dependency modification or blanket noncomputable conversion is used.

Every invocation has its own memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable. Observations are not reservations or peak-memory guarantees. The admission helper and exclusive supervisor are unchanged. Every compiler/checker is sequential under the universal exclusive lock, with a unique UUID, persisted preflight, submitted source snapshots/hashes, child PID, exact argv/options, UTC/monotonic times, exit and reaping. The legacy comparison uses accepted objects; current audit/replay use isolated current outputs and pinned packages without historical project fallback.

The unchanged unfiltered audit covers 9162 actual-owner project roots, 60581 recursive constants and 48 opaque bodies, recursively traversing types/bodies, generated declarations, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms. No unsafe project roots or aggregate-owned declarations occur. Exactly the value companion disappears, while all other 32 partial roots remain. The strict audit exits 1 with 64 root/recursive findings. No violation is filtered, exempted or allowlisted.

The official resolver selects exactly LightEFTSpanners.StoredWeightLookup; the supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredWeightLookup` passes with exactly one replay line. No aggregate-prefix replay occurs. Singleton replay does not discharge the remaining partials or replace the required clean final exact-source gate.

## Raw evidence and review boundary

136 source-bound receipts contain 626 submitted-source entries and matching preflights/memory admissions. Reconciliation verifies snapshots, UUID uniqueness, one lock inode, non-overlap, child reaping, exact closure and inherited provenance. Zero anchored warning headers occur; hints and option names are not counted as warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID 506b56fa2365449dad826b5455bd99be. No legacy proof, production compile or fixture failed in this checkpoint. Its complete diagnostic and submitted source snapshots remain preserved.

All historical trees and failures remain byte-identical, including the prior rowValue legacy attempt's error-recovery sorryAx output, historical aggregate-prefix OOM/sequencing qualification, prior statement-count correction and evidence-writer-label correction. UUID directories preserve authoritative raw logs; semantic-label logs are convenience copies.

The complete recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives per-chunk hashes and the whole-file reconstruction hash; concatenate bytes in manifest order without added headers or separators. evidence-sha256.json seals all checkpoint files except itself.

reconcile.py is an evidence writer: it regenerates current derived evidence/chunks without running Lean/checker and checks historical manifests without modifying them. Entry points: legacy_compare.py; run.py pilot/build/audit/replay; reconcile.py. No compiler/checker runs during publication reconciliation. Terminal resource/process/lock and repository-wide active CI observations are saved. Additive source/evidence commits use [skip ci], with normal push after remote-state verification. Paused for independent review; no other target is started.

Minimum observed cgroup headroom: 8701427712 bytes; minimum system MemAvailable: 17408430080 bytes.

Current checkpoint observed free disk: initially 17.86 GiB (19174891520 bytes), terminal 17.77 GiB (19083845632 bytes).
