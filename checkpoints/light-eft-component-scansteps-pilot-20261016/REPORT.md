# StoredComponentHostFilter.scanSteps total-recursor pilot

Tested source: `7ed0406cdb2302980d56d94b324fe978affdc2cd`. Branch: `light-eft-spanners-checkpoints`. Exact source/object bindings are in `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredComponentHostFilter.scanSteps._unsafe_rec` disappears: **25 → 24 partial roots**, none added. The unchanged exhaustive strict gate still fails with **48 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and precision correction

The parent accepted source `f015b5c0a68e1338d70b208cd88b6db1d5ea0624` and evidence `defd01fab1d12d4a6d44e4a76f0e68d652bdb4a3`; review had finished before this work. This records source/log/hash reconciliation, not fresh independent execution or live-object inspection. The environment reported ready; live commands then checked accepted state, resources, processes and the common lock. All 1,194 parent-manifest entries and all 486 live source/object bindings matched. No Lean/Lake/checker was active, the lock was free and resources met admission thresholds. No other paper, canceled workspace or website was accessed in this task.

Additive precision correction, without rewriting historical evidence: the previous report's 7,163,920,384-byte figure is the minimum **memory-admission** headroom. Its locked preflight `ac0a551d767345f9a04daea11c4237c0` observed **7,163,887,616 bytes**. Both exceed the 4,294,967,296-byte threshold. `evidence/prior-precision-correction.json` reconciles both directly against preserved records. The prior same-PID/original-session observations support recorded build continuity and non-overlap of recorded attempts; they do not prove the absence of unrecorded execution. Historical task-routing and execution qualifications remain preserved.

Each current invocation has a separate persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, followed by the unchanged locked preflight. These are distinct observations, not reservations or peak-use guarantees. MemoryAdmission.py and the common exclusive supervisor are unchanged. One worker/compiler/checker is used, with no concurrent review.

## Exact scan count and unchanged reversal

The declaration is `LightEFTSpanners.StoredComponentHostFilter.scanSteps`; its actual owning module is **LightEFTSpanners.StoredComponentHostTrace**. The replacement uses total `List.rec` with base one and cons function `edgeSteps vs e + rest`. Nil and cons equations are proved by rfl. No condition is imposed on vertex or edge lists: empty lists, duplicates, loops, absent endpoints and arbitrary natural labels remain permitted.

The count includes the final scan-to-reversal transition. The sibling `steps` still adds `(value vs es).length + 1` for reversal; this pilot does not merge or remove that charge. `edgeSteps`, selected, State, transition, value, steps and bound remain unchanged. The entire StoredComponentHostFilter source file is unchanged. Only StoredComponentHostTrace changes: scanSteps, two new equations, and three simplification arguments in existing proofs. Its six existing theorem headers and hypotheses are unchanged; all other proof bodies are unchanged apart from those three arguments. All other 485 closure source files remain unchanged.

LegacyEquivalence.lean imports the exact hash-bound accepted object and proves equality of the complete natural count for every vertex list and edge list by induction and congrArg. Its replacement body is identical to production. The successful equality theorem is axiom-free.

Twenty exact-count fixtures cover empty inputs, loops, left/right endpoint absence, selected edges, reordered/duplicate vertex lists, duplicate/reversed edges, huge naturals and long lists. Universal equation checks include the separate reversal charge. Metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. Formal count preservation is not a physical-runtime claim.

## Sequential validation

Independent source-import analysis derives **88 affected strict builds** including aggregate compilation and **398 inherited objects**. Every affected entry was removed from build state before compiling, so intermediate object equality cannot skip an affected module. The unchanged inherited sources, objects and direct-import hashes are checked. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency revisions remain pinned, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Every runner verifies dependency revisions. Toolchain, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`; no default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable change is used.

The unchanged exhaustive audit, apart from output-directory substitution, covers 9100 actual-owner roots, 60519 recursive constants and 48 opaque bodies. It traverses generated declarations, types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms. No unsafe project roots or aggregate-owned declarations occur. Exactly the targeted partial companion disappears; all other 24 partial roots remain. The unfiltered audit exits 1 with 48 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official singleton resolution selects **LightEFTSpanners.StoredComponentHostTrace**, not the declaration namespace. The supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredComponentHostTrace` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit and replay use isolated current outputs and pinned packages with no historical project fallback; legacy equality uses separately hash-bound accepted objects. This is incremental validation, not the clean final exact-source gate.

## Evidence and remaining scope

93 unique source-bound receipts contain 583 submitted-source entries with persisted preflights and individual memory admissions. Each records exact argv/options, source snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation checks UUID uniqueness, one lock inode, recorded non-overlap, reaping, complete affected closure, inherited provenance and historical preservation. Receipt evidence is not proof against unrecorded execution. Zero anchored Lean warning headers occur; hints and option names are not counted as warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID e71f09e14e41428193dff8010e3ea012. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees and raw failures remain unchanged. The full recursive TSV and 207 ordered row-aligned chunks are preserved. `audit-export/manifest.json` supplies individual hashes and the whole-file reconstruction hash. Concatenate chunk bytes in order without extra headers or separators. `evidence-sha256.json` seals every checkpoint file except itself.

`reconcile.py` rewrites current derived evidence/chunks without invoking Lean/checker; it verifies historical manifests without modifying them. Entry points are legacy_compare.py, run.py pilot/build/audit/replay and reconcile.py. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal resources/process/lock and repository-wide CI observations are retained. Paused for independent review; no other target is started. Strict audit failure, clean final exact-source validation, Theorem 34, physical runtime and whole-paper completion remain open.

Current minimum observed memory-admission cgroup headroom: 6943072256 bytes; current minimum locked-preflight headroom: 6942359552 bytes. Minimum memory-admission system MemAvailable: 17376829440 bytes. These distinct observations do not certify continuous headroom.

Disk free after initial object copy: 17514037248 bytes (16.31 GiB); terminal: 17423847424 bytes (16.23 GiB). Cgroup limit: 17179869184 bytes. No local Lean/Lake/checker remains; common lock is free.
