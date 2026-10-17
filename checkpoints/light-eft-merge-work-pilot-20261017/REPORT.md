# StoredWeightMerge.work total-recursor pilot

Tested source: `67cc26bbae67c79cfd36ada18dce53b876d6333b`. Branch: `light-eft-spanners-checkpoints`. Exact source/object bindings are recorded in `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. It removes exactly `LightEFTSpanners.StoredWeightMerge.work._unsafe_rec`: **15 → 14 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **28 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and admission

The parent accepted source `1df836a762e8a80187e5575b7a9580349f8acdd2` and evidence `1aad3b4a3daaed9b98637d9c9ebe485875dadb9f`, and stated review had finished. This records source/log/hash reconciliation, not fresh independent execution or live-object inspection.

The parent reported a disconnect event at 00:46 during the completed prior turn (minute precision). Current live commands verified the connection, clean accepted tracked state, resources, processes and common lock before compiler admission. All 1,359 parent-manifest entries and all 486 live source/object bindings matched. No Lean/Lake/checker was active; the lock was free. Initial free disk was 15,566,401,536 bytes (14.50 GiB), with a 17,179,869,184-byte memory limit. Exact resource observations are retained. No compiler/checker was resumed or duplicated. `evidence/connection-recovery.json` records the reconciliation; current observations do not establish uninterrupted historical connectivity or exclude unrecorded execution. This task accessed no other paper, deleted workspace or website.

Every compiler/checker invocation has a persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, followed by the unchanged locked preflight. These distinct observations are not reservations, continuous-headroom certificates or peak-use guarantees. MemoryAdmission.py and the common exclusive supervisor are unchanged. One worker/compiler/checker is used with no concurrent review. All historical failure and recovery evidence, memory-precision qualifications, receipt-label corrections, and the prior wrong-scope SCC detour qualification remain preserved unchanged. Recorded process continuity does not prove absence of unrecorded execution.

## Exact arbitrary-input merge count

`StoredWeightMerge.work`, owned by module **StoredWeightMergeTrace**, now uses nested total `List.rec`. The outer recursor supplies the complete next-left-list function; the inner recursor supplies the next-right-list result. Empty-left and empty-right cases retain the other list's length plus 2. For two nonempty lists the count is exactly `StoredWeightComparison.steps bank x y + 2`, plus the old selected branch: shrink the left list if `result bank x y` is true, otherwise shrink the right list. Three equations establish both empty cases and the two-branch recurrence; the cons equation is rfl.

Comparison orientation is unchanged: `value y bank ≤ value x bank`, so ties select the left branch. The theorem covers every bank and both arbitrary input lists, including negative weights, duplicate keys, missing keys, reversed endpoint encodings, loops, unsorted/repeated lists and out-of-range labels. No sorting, validity, nonnegativity, uniqueness or graph premise is added. Exact formal count equality is not a claim about the physical evaluation cost of nested recursors.

The work count reaches the reversal state. The separate final reversal remains charged by `out.reverse.length + 1` in the unchanged full_trace statement/proof in StoredWeightMergeBound; it is not included in work or omitted from full execution.

Only StoredWeightMergeTrace.lean and StoredWeightMergeBound.lean change among the 486 production sources. The sole preexisting owner theorem merge_trace has an unchanged header and hypotheses; its only proof edits select the new equations in simplification arguments. In StoredWeightMergeBound, only three simplification lists in work_le change. All three existing theorem headers, bound, execute, and the other proofs are unchanged. StoredWeightMerge's state/transition and other sibling modules remain byte-identical. Initial proof-interface adjustments preceded compilation. The first bound-file compile reported six unused simplification arguments as errors under warningAsError; a second edit narrowed each list to its applicable equation. The failed source snapshot and all raw diagnostics are preserved. No statement or policy was weakened.

LegacyEquivalence.lean imports the exact hash-bound accepted owner object and proves universal complete natural-result equality by induction on the left list and then the right list. The cons case rewrites both induction hypotheses, covering both shrinking-list branches with the original Boolean test. The replacement body is identical to production. The proof reports exactly propext, Classical.choice and Quot.sound, with no sorryAx or additional axiom; it is not described as axiom-free.

Twenty-four focused exact-count fixtures cover both empty-side cases, both shrinking branches, ties choosing left, negative rational weights, duplicate bank keys with first-match lookup, reversed endpoint pairs, missing keys, unsorted lists, loops, huge labels and long lists/banks. Fixtures with unequal list lengths make branch selection affect the complete result. `evidence/fixture-expectations.json` records literal expected counts and independently computed lookup/branch charges. Universal equation examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion.

## Complete sequential validation

Source-import analysis and an independent fixed-point computation derive **28 affected strict builds**, including aggregate compilation, and **458 inherited objects**. Dependency order is verified. Every affected entry was removed from build state before compilation, so unchanged intermediate object bytes cannot skip affected recompilation. Inherited source/object/direct-import hashes are checked against the accepted checkpoint. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions. Executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable change is used.

The exhaustive audit is unchanged except output-directory substitution. It covers 9029 actual-owner roots, 60448 recursive constants and 48 opaque bodies, including generated declarations, types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms. No unsafe project roots or aggregate-owned declarations occur. Exactly the targeted work companion disappears; all other 14 partial roots remain. The unfiltered audit exits 1 with 28 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official singleton resolution selects **LightEFTSpanners.StoredWeightMergeTrace**. The supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredWeightMergeTrace` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages with no historical project fallback; legacy equality uses separately hash-bound accepted objects. This is incremental validation, not the clean final exact-source gate.

## Evidence and remaining scope

34 unique source-bound receipts contain 524 submitted-source entries with individual persisted preflights/memory admissions. Each records exact argv/options, source snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies UUID uniqueness, one lock inode, non-overlap of recorded attempts, all children reaped, affected closure, inherited provenance and historical preservation. Zero anchored Lean warning headers occur; hints and option names are not warnings.

Two nonzero compiler invocations are preserved: the bound-file attempt ee7103c247ae401db0ad67443d72a3b0 reported six unusedSimpArgs errors under warningAsError and was repaired by narrowing the three simplification lists; the unchanged exhaustive audit rejected remaining partial roots (UUID 4b0e429a72ef41569e955c4a5da0f810). Raw diagnostics and source snapshots for both remain intact. All final production builds, equality proof, fixtures and singleton replay passed. No linter or warning policy was disabled.

All historical checkpoint trees and raw failures remain unchanged. The full recursive TSV and 207 ordered row-aligned chunks are preserved. `audit-export/manifest.json` gives each chunk's bytes/hash and whole-file reconstruction hash. Concatenate bytes in order without extra headers/separators. `evidence-sha256.json` seals every checkpoint file except itself.

`reconcile.py` rewrites current derived evidence/chunks without invoking Lean/checker and verifies historical manifests without modifying them. Entry points are legacy_compare.py, run.py pilot/build/audit/replay and reconcile.py. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal process/lock/resources and repository-wide CI observations are retained. Paused for independent review; no other target is started. Strict audit failure, clean final exact-source validation, Theorem 34, physical runtime and whole-paper completion remain open.

Minimum observed memory-admission cgroup headroom: 4889673728 bytes; minimum locked-preflight headroom: 4889640960 bytes. Minimum memory-admission system MemAvailable: 17471864832 bytes. These distinct observations do not certify continuous headroom.

Terminal free disk: 15477772288 bytes (14.41 GiB). Terminal compiler/checker processes: none; common lock free.
