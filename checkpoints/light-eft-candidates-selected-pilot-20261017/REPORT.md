# StoredCandidates.selected total-recursor pilot

Tested source: `be9acc66ab0829b16a4f6adefd40f8ef4119358c`. Branch: `light-eft-spanners-checkpoints`. Exact source/object bindings are recorded in `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. It removes exactly `LightEFTSpanners.StoredCandidates.selected._unsafe_rec`: **13 → 12 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **24 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and admission

The parent accepted source `8b9f1fcf5cdda6561390f10e6f96737abe85a8d8` and evidence `e16ea5140067f206ef06dadcf2c1159a7d05ad42`, and stated review had finished. This records source/log/hash reconciliation, not fresh independent execution or live-object inspection.

The parent reported a disconnect at 01:34 during the completed prior turn (minute precision). Current live commands verified the connection, clean accepted tracked state, resources, processes and common lock before compiler admission. All 1,520 parent-manifest entries and all 486 live source/object bindings matched. No Lean/Lake/checker was active; the lock was free. Initial free disk was 15,151,689,728 bytes (14.11 GiB), with a 17,179,869,184-byte memory limit. Exact resource observations are retained. No compiler/checker was resumed or duplicated. `evidence/connection-recovery.json` records the current reconciliation, and prior disconnect evidence remains unchanged; current observations do not establish uninterrupted historical connectivity or exclude unrecorded execution. This task accessed no other paper, deleted workspace or website.

Every compiler/checker invocation has a persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, followed by the unchanged locked preflight. These distinct observations are not reservations, continuous-headroom certificates or peak-use guarantees. MemoryAdmission.py and the common exclusive supervisor are unchanged. One worker/compiler/checker is used with no concurrent review. All historical failure and recovery evidence, memory-precision qualifications, receipt-label corrections, and the prior wrong-scope SCC detour qualification remain preserved unchanged. Recorded process continuity does not prove absence of unrecorded execution.

## Exact arbitrary-state final list

`StoredCandidates.selected`, owned by module **StoredCandidateTrace**, now uses total `List.rec` returning a function of E. The base function returns E unchanged. Each input applies the recursively supplied function to the original `updated Q E w h R`. Nil and cons equations are rfl. This preserves the complete ordered final list, not merely its length, membership, set of edges or a graph equivalence.

Universal equality covers every n, Q, arbitrary initial E, rational weight function, threshold h and input list. No positivity, sorting, validity, uniqueness, disjointness or other premise is added. Acceptance prepends the candidate edge exactly as before, while rejection preserves the accumulated state. Input order, repeated records, duplicate initial and inserted edges, and endpoint orientation are retained. Later decisions use the actual updated E.

Only StoredCandidateTrace.lean and StoredCandidateRefinement.lean change among the 486 production sources. The owner prefix through updated is byte-identical, as is the entire suffix from work onward: repaired work, work_nil/work_cons, candidate_trace/candidates_trace and their proofs remain unchanged. All four existing owner theorem headers are preserved. In StoredCandidateRefinement, only the selected_eq_fold simplification argument changes to selected_cons. All three existing theorem headers, every definition including ValidSchedule, and all other proof text are unchanged. This interface change preceded compilation.

LegacyEquivalence.lean imports the exact hash-bound accepted owner object and proves universal complete final-list equality by list induction generalizing E. The cons case applies the induction hypothesis at precisely `updated Q E w h R`. The replacement body is identical to production. The proof reports exactly propext, Classical.choice and Quot.sound, with no sorryAx or additional axiom; it is not axiom-free.

Twenty-four complete final-list fixtures cover zero vertices, empty input preserving a nontrivial E, exact prepend order, duplicate input/initial edges, negative weights/budgets, empty hosts/draws, accept-all and reject-all cases, mixed acceptance/rejection, reverse endpoint orientation, duplicate hosts, and sixteen-record lists. State-feedback fixtures distinguish one insertion followed by rejection from repeated acceptance when Q excludes the inserted edge from sampling. Four explicit update fixtures check initial acceptance, updated-state rejection, Q exclusion allowing duplicate acceptance, and ordered prepend. Universal equation examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. No physical-runtime claim about recursor evaluation is made.

## Complete sequential validation

Source-import analysis and an independent fixed-point computation derive **150 affected strict builds**, including aggregate compilation, and **336 inherited objects**. Dependency order is verified. Every affected entry was removed from build state before compilation, so unchanged intermediate object bytes cannot skip affected recompilation. Inherited source/object/direct-import hashes are checked against the accepted checkpoint. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions. Executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable change is used.

The exhaustive audit is unchanged except output-directory substitution. It covers 9014 actual-owner roots, 60433 recursive constants and 48 opaque bodies, including generated declarations, types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms. No unsafe project roots or aggregate-owned declarations occur. Exactly the targeted selected companion disappears; all other 12 partial roots remain. The unfiltered audit exits 1 with 24 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official singleton resolution selects **LightEFTSpanners.StoredCandidateTrace**. The supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredCandidateTrace` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages with no historical project fallback; legacy equality uses separately hash-bound accepted objects. This is incremental validation, not the clean final exact-source gate.

## Evidence and remaining scope

155 unique source-bound receipts contain 645 submitted-source entries with individual persisted preflights/memory admissions. Each records exact argv/options, source snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies UUID uniqueness, one lock inode, non-overlap of recorded attempts, all children reaped, affected closure, inherited provenance and historical preservation. Zero anchored Lean warning headers occur; hints and option names are not warnings.

The only nonzero locked compiler/checker invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID 9fa9c520eadc44009a23c2f9dcad238a. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees and raw failures remain unchanged. The full recursive TSV and 207 ordered row-aligned chunks are preserved. `audit-export/manifest.json` gives each chunk's bytes/hash and whole-file reconstruction hash. Concatenate bytes in order without extra headers/separators. `evidence-sha256.json` seals every checkpoint file except itself.

`reconcile.py` rewrites current derived evidence/chunks without invoking Lean/checker and verifies historical manifests without modifying them. Entry points are legacy_compare.py, run.py pilot/build/audit/replay and reconcile.py. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal process/lock/resources and repository-wide CI observations are retained. Paused for independent review; no other target is started. Strict audit failure, clean final exact-source validation, Theorem 34, physical runtime and whole-paper completion remain open.

Minimum observed memory-admission cgroup headroom: 4445728768 bytes; minimum locked-preflight headroom: 4446253056 bytes. Minimum memory-admission system MemAvailable: 17228652544 bytes. These distinct observations do not certify continuous headroom.

Terminal free disk: 15059623936 bytes (14.03 GiB). Terminal compiler/checker processes: none; common lock free.
