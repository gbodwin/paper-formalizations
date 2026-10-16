# StoredVertexMembership.steps total-recursor pilot

Tested source: `405b6900f35b8231383af1b159cd0ad8848ba64f`. Branch: `light-eft-spanners-checkpoints`. Exact source/object bindings: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredVertexMembership.steps._unsafe_rec` disappears: **24 → 23 partial roots**, none added. The unchanged exhaustive strict gate still fails with **46 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Baseline and admission

The parent accepted source `7ed0406cdb2302980d56d94b324fe978affdc2cd` and evidence `551ab3cda20b0ec4a1b301dad24d8b33908ab464`; review finished before this work. This records source/log/hash reconciliation, not fresh independent execution or live-object inspection.

The environment returned ready and live commands verified the accepted tracked state, processes, resources and lock before compiler admission. All 1,210 parent-manifest entries and all 486 live source/object bindings matched. No Lean/Lake/checker was active, the common lock was free and resources met admission thresholds. No other paper, canceled workspace or website was accessed in this task.

Every invocation has its own persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, followed by the unchanged locked preflight. These are distinct observations, not reservations, continuous-headroom certificates or peak-use guarantees. MemoryAdmission.py and the common exclusive supervisor are unchanged. One worker/compiler/checker is used with no concurrent review. Historical distinctions between recorded same-PID continuity and unproven absence of unrecorded execution, and between admission versus locked-preflight memory samples, remain preserved.

## Exact membership count

`StoredVertexMembership.steps` now uses total `List.rec`, with base 1 and cons function `if v=x then 1 else rest+1`. Two equations are proved by rfl. It preserves the empty-input count 1, matching-head count 1, and nonmatching-head tail count plus 1 for every natural query and arbitrary natural list. No sortedness, uniqueness, bound, membership or validity hypothesis is added.

The entire prefix before steps is byte-identical, including State, transition and **contains**. All other definitions remain unchanged. Only this production file changes. Its three preexisting theorem headers and hypotheses are unchanged. Three simplification arguments in scan_trace and steps_le now use steps_cons; contains_iff and all other proof text remain unchanged. These anticipated interface adjustments preceded compilation. All other 485 closure source files are unchanged.

LegacyEquivalence.lean imports the exact hash-bound accepted object and proves complete natural-result equality for every v and xs by induction and congrArg of the same conditional step. The replacement body is identical to production. The successful theorem is axiom-free.

Twenty focused exact-count fixtures cover empty inputs, a matching head, a nonmatching head, first matches at different positions, absence, duplicate values and first-match behavior, huge naturals and long matching/nonmatching tails. Universal nil/cons equation examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. This preserves the formal controller count; it does not assert that recursor evaluation physically stops at the matching head or prove physical-runtime complexity.

## Complete sequential validation

Source-import analysis and a separate fixed-point check derive **90 affected strict builds**, including aggregate compilation, and **396 inherited objects**. Dependency order is verified. Every affected entry was removed from build state before compilation, so equal intermediate object bytes cannot skip affected recompilation. Inherited source/object/direct-import hashes are checked against the accepted checkpoint. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions. Exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable change is used.

The exhaustive audit is unchanged except output-directory substitution. It covers 9096 actual-owner roots, 60515 recursive constants and 48 opaque bodies, including generated declarations, types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms. No unsafe project roots or aggregate-owned declarations occur. Exactly the targeted steps companion disappears; all other 23 partial roots remain, including the unchanged contains companion. The unfiltered audit exits 1 with 46 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official singleton resolution selects the actual owner **LightEFTSpanners.StoredVertexMembership**. The supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredVertexMembership` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages with no historical project fallback; legacy equality uses separately hash-bound accepted objects. This is incremental validation, not the clean final exact-source gate.

## Evidence and remaining scope

95 unique source-bound receipts contain 585 submitted-source entries with individual persisted preflights/memory admissions. Each records exact argv/options, submitted-source snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies UUID uniqueness, one lock inode, non-overlap of recorded attempts, all children reaped, affected closure, inherited provenance and historical preservation. Recorded receipt continuity does not prove absence of unrecorded execution. Zero anchored Lean warning headers occur; hints and option names are not warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID 20aa5ef3eb3f459c8f9c8a4bbc6e0b85. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees and raw failures are unchanged. The full recursive TSV and 207 ordered row-aligned chunks are preserved. `audit-export/manifest.json` gives per-chunk bytes/hashes and whole-file reconstruction hash. Concatenate chunk bytes in manifest order without additional headers/separators. `evidence-sha256.json` seals every checkpoint file except itself.

`reconcile.py` rewrites current derived evidence/chunks without invoking Lean/checker and checks historical manifests without modifying them. Entry points are legacy_compare.py, run.py pilot/build/audit/replay and reconcile.py. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal process/lock/resources and repository-wide CI observations are retained. Paused for independent review; no other target is started. Strict audit failure, clean final exact-source validation, Theorem 34, physical runtime and whole-paper completion remain open.

Current minimum observed memory-admission cgroup headroom: 6724534272 bytes; current minimum locked-preflight headroom: 6724476928 bytes. Minimum memory-admission system MemAvailable: 17373736960 bytes. These distinct observations do not certify continuous headroom.

Disk free after initial object copy: 17306812416 bytes (16.12 GiB); terminal: 17216552960 bytes (16.03 GiB). Cgroup limit: 17179869184 bytes. No local Lean/Lake/checker remains; common lock is free.
