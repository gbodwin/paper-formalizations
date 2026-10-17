# StoredComponentCatalogue.scanSteps total-recursor pilot

Tested source: `7294788bc74a77ef64f57819883a80011044f8b8`. Branch: `light-eft-spanners-checkpoints`. Exact source/object bindings are recorded in `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. It removes exactly `LightEFTSpanners.StoredComponentCatalogue.scanSteps._unsafe_rec`: **18 → 17 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **34 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and admission

The parent accepted source `c2e0727cf18f2d453602a92c749c6a7829f92ae3` and evidence `23ebaaf25f67f9b77c2584efd698c3bc4f1df0d9`, and stated review had finished. This records source/log/hash reconciliation, not fresh independent execution or live-object inspection.

Live commands verified the connection, clean accepted tracked state, resources, processes and common lock before compiler admission. All 1,461 parent-manifest entries and all 486 live source/object bindings matched. No Lean/Lake/checker was active; the lock was free. Initial free disk was 16,049,893,376 bytes (14.95 GiB), with a 17,179,869,184-byte memory limit. Exact resource observations are retained. This task accessed no other paper, deleted workspace or website.

Every compiler/checker invocation has a persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, followed by the unchanged locked preflight. These distinct observations are not reservations, continuous-headroom certificates or peak-use guarantees. MemoryAdmission.py and the common exclusive supervisor are unchanged. One worker/compiler/checker is used with no concurrent review. All historical failure and recovery evidence, memory-precision qualifications, receipt-label corrections, and the prior wrong-scope SCC detour qualification remain preserved unchanged. Recorded process continuity does not prove absence of unrecorded execution.

## Exact arbitrary-input scan count

`StoredComponentCatalogue.scanSteps` now uses total `List.rec` with base 1 and cons function `StoredComponentRecord.steps r + 2 + rest`. Nil and cons equations are proved by rfl. It preserves the complete natural result for every arbitrary input list, without validity, identifier, vertex-bound, uniqueness, disjointness, simplicity or payload assumptions.

The base counts the final scan-to-reversal transition. Each input contributes its exact record-machine count plus two outer transitions. The final catalogue reversal remains separately charged as `rs.length + 1` in the unchanged `bank_trace` statement. The component-record count already includes its own vertex-pair-machine work; no inner or outer reversal is omitted or conflated.

Only StoredComponentCatalogue.lean changes among the 486 production sources. State, transition, result and inputBound remain byte-identical. All five existing theorem headers and hypotheses remain unchanged. The only proof adjustments are one simplification argument in inputs_trace and two in steps_le_input, using the new cons/nil equations. These adjustments preceded compilation. The bank target definitions and other siblings are untouched.

LegacyEquivalence.lean imports the exact hash-bound accepted owner object and proves universal complete natural-result equality by induction and congrArg of the exact record-count-plus-two expression. Its replacement body is identical to production. The successful theorem is axiom-free.

Twenty focused exact-count fixtures cover empty catalogues, empty vertex lists, singleton/two/three/four-element lists, duplicate vertices, repeated records and identifiers, arbitrary host/draw payloads, huge natural labels, sixteen-record lists, and sixteen/thirty-two-vertex records. They check complete scan counts, including base 1 and every record count plus two. Universal nil/cons examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. This formal count equality is not a physical-runtime claim about recursor evaluation.

## Complete sequential validation

Source-import analysis and an independent fixed-point computation derive **115 affected strict builds**, including aggregate compilation, and **371 inherited objects**. Dependency order is verified. Every affected entry was removed from build state before compilation, so unchanged intermediate object bytes cannot skip affected recompilation. Inherited source/object/direct-import hashes are checked against the accepted checkpoint. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions. Executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable change is used.

The exhaustive audit is unchanged except output-directory substitution. It covers 9058 actual-owner roots, 60477 recursive constants and 48 opaque bodies, including generated declarations, types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms. No unsafe project roots or aggregate-owned declarations occur. Exactly the targeted catalogue scanSteps companion disappears; all other 17 partial roots remain. The unfiltered audit exits 1 with 34 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official singleton resolution selects **LightEFTSpanners.StoredComponentCatalogue**. The supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredComponentCatalogue` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages with no historical project fallback; legacy equality uses separately hash-bound accepted objects. This is incremental validation, not the clean final exact-source gate.

## Evidence and remaining scope

120 unique source-bound receipts contain 610 submitted-source entries with individual persisted preflights/memory admissions. Each records exact argv/options, source snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies UUID uniqueness, one lock inode, non-overlap of recorded attempts, all children reaped, affected closure, inherited provenance and historical preservation. Zero anchored Lean warning headers occur; hints and option names are not warnings.

The only nonzero locked compiler/checker invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID 42f6f635361b4a6eba8d7daa67f2987e. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees and raw failures remain unchanged. The full recursive TSV and 207 ordered row-aligned chunks are preserved. `audit-export/manifest.json` gives each chunk's bytes/hash and whole-file reconstruction hash. Concatenate bytes in order without extra headers/separators. `evidence-sha256.json` seals every checkpoint file except itself.

`reconcile.py` rewrites current derived evidence/chunks without invoking Lean/checker and verifies historical manifests without modifying them. Entry points are legacy_compare.py, run.py pilot/build/audit/replay and reconcile.py. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal process/lock/resources and repository-wide CI observations are retained. Paused for independent review; no other target is started. Strict audit failure, clean final exact-source validation, Theorem 34, physical runtime and whole-paper completion remain open.

Minimum observed memory-admission cgroup headroom: 5387165696 bytes; minimum locked-preflight headroom: 5387116544 bytes. Minimum memory-admission system MemAvailable: 17331994624 bytes. These distinct observations do not certify continuous headroom.

Terminal free disk: 15958863872 bytes (14.86 GiB). Terminal compiler/checker processes: none; common lock free.
