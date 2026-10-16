# StoredEdges.steps total-recursor pilot

Tested source: `d7b14b8e8e2af7142cc17269e07930eb470a709e`. Branch: `light-eft-spanners-checkpoints`. Exact source/object bindings: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredEdges.steps._unsafe_rec` disappears: **22 → 21 partial roots**, none added. The unchanged exhaustive strict gate still fails with **42 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Baseline and fresh capacity

The parent accepted source `f87e4853956cbae507c8f0fa54ba0887ce58ab52` and evidence `95b9a09e53a85ad2c1b59d79f5d7bbca37bf608f`; review finished before this work. This records source/log/hash reconciliation, not fresh independent execution or live-object inspection.

Live commands verified connection, accepted tracked state, processes, resources and lock before compiler admission. All 1,219 parent-manifest entries and all 486 live source/object bindings matched. No Lean/Lake/checker was active and the common lock was free. Fresh capacity was checked for the larger closure: 176 affected modules, 310 inherited objects, approximately 107 MB of copied project objects, over 15 GiB free disk and over 5 GiB initial cgroup headroom. Exact bytes and times are retained. No other paper, canceled workspace or website was accessed in this task.

Every invocation has its own persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, followed by the unchanged locked preflight. These are distinct observations, not reservations, continuous-headroom certificates or peak-use guarantees. MemoryAdmission.py and the common exclusive supervisor are unchanged. One worker/compiler/checker is used with no concurrent review. Historical distinctions between recorded same-PID continuity and unproven absence of unrecorded execution, and between admission versus locked-preflight memory samples, remain preserved.

## Exact arbitrary endpoint-pair counts

The declaration is `LightEFTSpanners.StoredEdges.steps`; its actual owning module is **LightEFTSpanners.StoredEdgeMembership**. It now uses total `List.rec`, with base 1 and cons function `if same q e then 1 else rest+1`. Two equations are proved by rfl. The empty count is 1, a matching stored pair costs 1, and a nonmatching head costs the tail count plus 1 for every query pair and arbitrary pair list. No graph validity, distinct-endpoint, orientation, vertex-bound, uniqueness, sortedness or membership hypothesis is added.

`same` is unchanged, including its direct-or-reversed endpoint comparison. `contains`, Edge, State, transition and encode are unchanged. Only StoredEdgeMembership changes: steps, two new equations and three simplification arguments in scan_trace/steps_le. All six existing theorem headers and hypotheses are unchanged, and all other proof text is unchanged. These anticipated interface adjustments preceded compilation. All other 485 closure source files remain unchanged; no second target is repaired.

LegacyEquivalence.lean imports the exact hash-bound accepted owner object and proves equality of the complete natural result for every query q and list es by induction and congrArg of the same conditional. Its replacement body is identical to production. The successful theorem is axiom-free.

Twenty exact-count fixtures cover empty input, direct and reversed matches, loops and loop/nonloop mismatches, absent/shared endpoints, first matches at different positions, duplicate pairs, huge naturals and long matching/nonmatching lists. Universal nil/cons examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. This is exact formal controller-count equality, not a claim that recursor evaluation physically short-circuits or a physical-runtime theorem. The unchanged transition still describes the inherited short-circuit controller.

## Complete sequential validation

Source-import analysis and a separate fixed-point check derive **176 affected strict builds**, including aggregate compilation, and **310 inherited objects**. Dependency order is verified. Every affected entry was removed from build state before compilation, so equal intermediate object bytes cannot skip affected recompilation. Inherited source/object/direct-import hashes are checked against the accepted checkpoint. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions. Exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable change is used.

The exhaustive audit is unchanged except output-directory substitution. It covers 9084 actual-owner roots, 60503 recursive constants and 48 opaque bodies, including generated declarations, types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms. No unsafe project roots or aggregate-owned declarations occur. Exactly the targeted steps companion disappears; all other 21 partial roots remain, including the unchanged StoredEdges.contains companion. The unfiltered audit exits 1 with 42 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official singleton resolution selects **LightEFTSpanners.StoredEdgeMembership**, not the declaration namespace StoredEdges. The supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredEdgeMembership` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages with no historical project fallback; legacy equality uses separately hash-bound accepted objects. This is incremental validation, not the clean final exact-source gate.

## Evidence and remaining scope

181 unique source-bound receipts contain 671 submitted-source entries with individual persisted preflights/memory admissions. Each records exact argv/options, submitted-source snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies UUID uniqueness, one lock inode, non-overlap of recorded attempts, all children reaped, affected closure, inherited provenance and historical preservation. Recorded receipt continuity does not prove absence of unrecorded execution. Zero anchored Lean warning headers occur; hints and option names are not warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID de619c48a29e4ac884a591a5a9de22b5. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees and raw failures are unchanged. The full recursive TSV and 207 ordered row-aligned chunks are preserved. `audit-export/manifest.json` gives per-chunk bytes/hashes and whole-file reconstruction hash. Concatenate chunk bytes in manifest order without additional headers/separators. `evidence-sha256.json` seals every checkpoint file except itself.

`reconcile.py` rewrites current derived evidence/chunks without invoking Lean/checker and checks historical manifests without modifying them. Entry points are legacy_compare.py, run.py pilot/build/audit/replay and reconcile.py. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal process/lock/resources and repository-wide CI observations are retained. Paused for independent review; no other target is started. Strict audit failure, clean final exact-source validation, Theorem 34, physical runtime and whole-paper completion remain open.

Current minimum observed memory-admission cgroup headroom: 6282870784 bytes; current minimum locked-preflight headroom: 6283653120 bytes. Minimum memory-admission system MemAvailable: 17347153920 bytes. These distinct observations do not certify continuous headroom.

Disk free after initial object copy: 16892235776 bytes (15.73 GiB); terminal: 16799444992 bytes (15.65 GiB). Cgroup limit: 17179869184 bytes. No local Lean/Lake/checker remains; common lock is free.
