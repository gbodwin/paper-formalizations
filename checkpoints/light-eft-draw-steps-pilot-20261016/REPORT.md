# StoredDrawLookup.steps total-recursor pilot

Tested source: `5ad25c7ecc138ae1a307c9a266d29bdb838e0438`. Branch: `light-eft-spanners-checkpoints`. Exact source/object binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredDrawLookup.steps._unsafe_rec` disappears: **29 → 28 partial roots**, none added. The unchanged exhaustive strict gate still fails with **56 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Baseline and connection

The parent accepted source `e5eeb9ae503b4ab31af5593f898f6cf43b09a2b0` and evidence `2b53161f41aa639bce27fdb02db1ca85a430923e`. Review had finished. This records source/log/hash reconciliation, not fresh reviewer execution or live-object inspection.

A disconnect was reported at 20:55 while the preceding turn was completed. Live commands succeeded before admission. HEAD and tracked source matched the accepted evidence, all 1,140 parent-manifest entries and all 486 live source/object bindings verified. No preceding build was resumed or duplicated. The actual steps declaration was inspected. No Lean/Lake/checker was active, the universal lock was free and resources met admission thresholds. Initial and terminal resource bytes and UTC times are retained; GiB uses 2^30 bytes. No canceled workspace, other paper or website was accessed or changed.

Each invocation has a separate persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, independently of the supervisor's disk gate. Observations are not reservations or peak-memory guarantees. MemoryAdmission.py and the exclusive supervisor are unchanged. No parallel worker or concurrent review was used.

## Exact first-match counts

The replacement uses explicit total List.rec. Empty banks return one. A matching head returns one, irrespective of payload. A nonmatching head returns one plus the tail count. The two equations are proved by rfl. This preserves the final halt count on misses and immediate termination for empty matching payloads; later duplicate keys cannot increase the count after a match.

LegacyEquivalence.lean imports exact hash-bound accepted objects and proves equality of the complete natural count for every key and arbitrary bank. Induction applies congrArg to the original conditional. The replacement body is identical to production and the successful theorem is axiom-free. No uniqueness, nonempty-payload, key-range, bank-validity or input-bound hypothesis is added.

Twenty exact-count fixtures cover empty banks, matches and misses, reversed duplicate ordering, empty matching payloads before nonempty duplicates, payloads containing empty inner draws, one/two skipped entries, large keys, long missing prefixes, complete misses, and long payloads that still cost one at a matching head. Universal equation examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. The claim is equality of formal transition counts, not physical runtime or recursor evaluation cost.

Only steps changes definition. The entire prefix before it remains byte-identical, including Bank, State, transition, repaired value and its equations. All four existing theorem headers and hypotheses remain unchanged. Four simplification arguments in lookup_trace and steps_le use the explicit steps equations; these anticipated proof-interface adjustments were made before compilation. Existing value equations and all other proof bodies remain unchanged. All other 485 closure source files, including typedValue and its encoding module, are byte-identical to the accepted baseline.

## Complete sequential validation

The source-import closure is independently recomputed: 74 fresh affected strict builds, including aggregate compilation, and 412 inherited objects retaining accepted source, direct-import and object hashes. Every affected state entry was removed before rebuilding so equal intermediate outputs cannot bypass compilation. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions; exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable changes occur.

The exhaustive audit is unchanged except output-directory substitution. It covers 9132 actual-owner project roots, 60551 recursive constants and 48 opaque bodies, including generated declarations, recursive types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. No unsafe project roots or aggregate-owned declarations occur. Exactly the steps companion disappears, while all other 28 partial roots remain. The strict audit exits 1 with 56 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official target resolution selects exactly LightEFTSpanners.StoredDrawLookup; the supervisor repeats resolution under the common lock. `leanchecker -v LightEFTSpanners.StoredDrawLookup` passes with one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages without historical project fallback; legacy equality uses separately hash-bound accepted objects. Singleton replay does not discharge the remaining partials or replace clean final exact-source validation.

## Receipts and preservation

79 unique source-bound receipts contain 569 submitted-source entries and individual persisted preflights/memory admissions. Each invocation records exact argv/options, snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies hashes, UUID uniqueness, one lock inode, strict non-overlap, all children reaped, full affected closure, inherited provenance and historical preservation. Zero anchored warning headers occur; hints and option names are not warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID 6c5801758d5b4b0891ea08497905100e. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees and raw failures remain unchanged, including prior legacy recovery output, metadata-harness failure, aggregate-prefix OOM/sequencing qualification, statement-count correction, evidence-writer-label correction and disk precision correction. UUID logs are authoritative; semantic-label logs are convenience copies.

The full recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives chunk hashes and the whole-file reconstruction hash; concatenate bytes in order without added headers or separators. evidence-sha256.json seals every checkpoint file except itself.

reconcile.py rewrites current derived evidence/chunks without running Lean/checker and checks historical manifests without modifying them. Entry points: legacy_compare.py; run.py pilot/build/audit/replay; reconcile.py. Publication reconciliation runs no compiler/checker. Source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal resource/process/lock and repository-wide CI observations are saved. Paused for independent review; no other target is started.

Minimum observed cgroup headroom: 7820406784 bytes; minimum system MemAvailable: 17400762368 bytes.

Current checkpoint observed free disk: initially 17.08 GiB (18341609472 bytes), terminal 17.00 GiB (18251722752 bytes).
