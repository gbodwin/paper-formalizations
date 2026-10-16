# StoredCanonicalHosts.scanSteps total-recursor pilot

Tested source: `f015b5c0a68e1338d70b208cd88b6db1d5ea0624`. Branch: `light-eft-spanners-checkpoints`. Exact source/object binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredCanonicalHosts.scanSteps._unsafe_rec` disappears: **26 → 25 partial roots**, none added. The unchanged exhaustive strict gate still fails with **50 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Baseline and admission

The parent accepted source `dde0905c34ad4c32fd0676014ac1af4ca4abd878` and evidence `406edcfd05c0cfb7218867ff0c98597e364e0fe7`; review had finished. This records source/log/hash reconciliation, not fresh reviewer execution or live-object inspection.

Live commands verified connection and clean accepted tracked state before compiler admission. All 1,134 parent-manifest entries and all 486 live source/object bindings matched. The actual scanSteps declaration and filter-count/bound consumers were inspected. No Lean/Lake/checker was active, the common lock was free, and resources met admission thresholds. Initial/terminal resource bytes and UTC times are retained; GiB uses 2^30 bytes. No canceled workspace or website was accessed or changed. A mistaken read-only SCC detour is disclosed below.

Each invocation has a separate persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, independently of the supervisor disk gate. Observations are not reservations or peak-use guarantees. MemoryAdmission.py and the common exclusive supervisor are unchanged. There is no parallel worker or concurrent review.

## Exact filter-plus-two scan counts

The replacement uses total List.rec with base one and cons function `StoredComponentHostFilter.steps r.2 edges + 2 + rest`. Its two equations are proved by rfl. The base counts the empty-record transition to reversal; the two cons transitions enter filtering and attach its result. The existing full filter budget, including its own scan and reversal, remains intact. The outer host reversal remains separately charged by unchanged sibling steps.

LegacyEquivalence.lean imports exact hash-bound accepted objects and proves equality of the complete natural result for every edge list and arbitrary component list. Induction applies congrArg to adding the exact filter-plus-two term. The replacement body is identical to production and the successful theorem is axiom-free. No valid-component, disjointness, uniqueness, vertex-bound, connectivity, edge-validity or acyclicity premise is added.

Twenty exact-count fixtures cover empty inputs and edge lists, loops, absent left/right endpoints, both endpoints present, reordered/duplicate vertex lists, duplicate and reversed edges, arbitrary component/root labels, repeated records, huge natural endpoints and long lists. The fixture counts include the complete per-component filter, both outer transitions and final scan base. Universal equation examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. Formal count equality is not a physical-runtime claim about recursor evaluation.

Two production files change. StoredCanonicalHosts.lean changes only scanSteps and adds two equations. The prefix including Component, Record, State, transition and value remains byte-identical. All four existing theorem headers retain their hypotheses; scan_trace changes one simplification argument to scanSteps_cons, while other proofs and sibling steps remain unchanged. StoredCanonicalHostsBound.lean changes two scanSteps_le simplification arguments to scanSteps_nil/scanSteps_cons. Both existing headers retain the original component-size hypothesis `h`; other proof bodies and bound remain unchanged. These anticipated interface adjustments were made before compilation. All other 484 closure source files are unchanged.

## Complete sequential validation

The independently recomputed source-import closure confirms 85 affected strict builds, including aggregate compilation, and 401 inherited objects retaining accepted source, direct-import and object hashes. This is derived from actual imports rather than assumed from the parent's estimate. Every affected state entry was removed before rebuilding so equal intermediate outputs cannot skip compilation. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency revisions remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions; exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable changes occur.

The exhaustive audit is unchanged except output-directory substitution. It covers 9108 actual-owner project roots, 60527 recursive constants and 48 opaque bodies, including generated declarations, recursive types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. No unsafe project roots or aggregate-owned declarations occur. Exactly the scanSteps companion disappears; all other 25 partial roots remain. The audit exits 1 with 50 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official resolution selects exactly LightEFTSpanners.StoredCanonicalHosts, and the supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredCanonicalHosts` passes with one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages without historical project fallback; legacy equality uses separately hash-bound accepted objects. Singleton replay does not discharge remaining partials or replace clean final exact-source validation.

## Evidence and preservation

90 unique source-bound receipts contain 580 submitted-source entries and individual persisted preflights/memory admissions. Each records exact argv/options, snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies hashes, UUID uniqueness, one lock inode, strict non-overlap, all children reaped, full affected closure, inherited provenance and historical preservation. Zero anchored warning headers occur; hints and option names are not warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID c7a9ae50b81743d3a28195ebe8482cc0. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees and raw failures remain unchanged, including prior forest encoding failure, legacy recovery output, metadata-harness failure, aggregate-prefix OOM/sequencing qualification, statement-count correction, evidence-writer-label correction and disk precision correction. UUID raw logs are authoritative; semantic-label logs are convenience copies.

The full recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives chunk hashes and the whole-file reconstruction hash; concatenate bytes in order without added headers or separators. evidence-sha256.json seals every checkpoint file except itself.

reconcile.py rewrites current derived evidence/chunks without running Lean/checker and checks historical manifests without modifying them. Entry points: legacy_compare.py; run.py pilot/build/audit/replay; reconcile.py. Publication reconciliation runs no compiler/checker. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal process/lock/resources and repository-wide CI observations are saved. Paused for independent review; no other target is started.

Minimum observed cgroup headroom: 7163920384 bytes; minimum system MemAvailable: 17474682880 bytes.

## Task-routing correction

During continuation, the worker mistakenly inspected and hash-reconciled existing SCC evidence and returned an unrelated endpoint. The parent corrected the active target. No SCC source was edited, no SCC compiler was run, and no SCC commit was pushed. The already-admitted Light EFT build (supervisor PID 94894, original session 28086) was not interrupted or duplicated. Its exact command was `python checkpoints/light-eft-canonical-scansteps-pilot-20261016/run.py build`, in `/workspace/light-eft-verification`, under the common lock. The original session was resumed and reported successful completion. Current receipt reconciliation confirms all 85 fresh builds and non-overlap. The unrelated response was not evidence for this checkpoint.

Disk free after initial object copy: 16.50 GiB; terminal: 16.42 GiB. No local Lean/Lake/checker remains; common lock is free.
