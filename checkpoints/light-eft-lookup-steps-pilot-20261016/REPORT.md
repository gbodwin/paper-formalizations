# StoredWeightLookup.steps total-recursor pilot

Tested source: `6c020d40a958aff19d7db7ec3592df3d107f997b`. Branch: `light-eft-spanners-checkpoints`. Source/object binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredWeightLookup.steps._unsafe_rec` disappears: **31 → 30 partial roots**, none added. The unchanged exhaustive strict gate still fails with **60 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Baseline and admission

The parent accepted source `041143e438c28bb4a4179dd8c6931a3422c788b3` and evidence `ff592080e3d8f12110132feae458269cfe876b06`. Review had finished before this work. This records source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

Connection and accepted tracked state were verified before admission. All 1,427 parent-manifest entries and all 486 live source/object bindings matched. The actual steps declaration was inspected. No Lean/Lake/checker was active, the common exclusive lock was free, and memory met both admission thresholds. Initial and terminal resources and UTC times are retained; disk GiB uses 2^30 bytes. No canceled workspace, other paper or website was accessed or changed.

Every invocation has an individual memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, separate from the supervisor's disk gate. Observations do not reserve memory or guarantee peak use. MemoryAdmission.py and the common exclusive supervisor are unchanged. No parallel worker or concurrent review was used.

## Unrestricted full-count equivalence

Explicit total List.rec over the outer matrix produces a function of the row index while keeping the column index fixed. Empty matrices return one. Row index zero returns unchanged rowSteps j row plus one for the row-to-cell transition. A successor row index returns the tail's count at the predecessor plus one for skipping the current row. Both successful and failed traversals retain the final transition to halt. The three equations are proved by rfl.

LegacyEquivalence.lean imports the exact hash-bound accepted implementation and proves equality of the complete natural count for every i,j and every rational list of lists. Induction generalizes i; the successor case applies congrArg to adding one. The replacement body is identical to production, and the successful theorem is axiom-free. There is no rectangularity, nonempty-row, in-range, sign or validity premise.

Twenty fixtures compare exact complete counts for empty matrices, empty selected rows, huge independent row/column indices, ragged signed fractional matrices, every selected-cell position, first and later cell misses, first and later row misses, and a 16-by-16 case distinguishing last-cell success (32), first cell miss (33), and row miss (17). Universal equation examples and metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. This preserves formal transition counts, not physical runtime or recursor evaluation cost.

Only steps changes definition. The entire prefix before it remains byte-identical, including State, transition, repaired rowValue, value, rowSteps and their equations. All sixteen existing theorem headers and hypotheses remain unchanged. Five simplification arguments in lookup_trace and steps_le use the explicit equations; these anticipated proof-interface adjustments were made before compilation. Every other existing proof body and all other 485 closure source files remain unchanged.

## Complete affected validation

The source-import closure is independently recomputed: 131 affected strict builds, including aggregate compilation, plus 355 inherited objects with accepted source, direct-import and object hashes. All affected state entries were removed before rebuilding so identical intermediate outputs cannot skip required compilation. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions. Exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, baseline weakening, alternate runtime or blanket noncomputable change occurs.

The exhaustive audit is unchanged except output-directory substitution. It covers 9144 actual-owner project roots, 60563 recursive constants and 48 opaque bodies, including generated declarations, recursive types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. No unsafe project roots or aggregate-owned declarations occur. No remaining partial is filtered or exempted. Exactly the steps companion disappears; the other 30 partial roots remain. The audit exits 1 with 60 root/recursive findings.

Official target resolution selects exactly LightEFTSpanners.StoredWeightLookup, and the supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredWeightLookup` passes with one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages without historical project fallback. Legacy equality uses separately hash-bound accepted objects. Singleton replay does not discharge other partials or replace the required clean final exact-source gate.

## Evidence and review boundary

136 unique source-bound receipts contain 626 submitted-source entries and matching persisted preflights/memory admissions. Each invocation records exact argv/options, snapshots/hashes, lock identity, child PID, UTC/monotonic times, exit and reaping. Reconciliation verifies every source snapshot, UUID uniqueness, one lock inode, non-overlap, all children reaped, inherited provenance, closure and historical preservation. Zero anchored warning headers occur; hints and option names are not warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID 28604d37b8a945b086436998ad69eb8f. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees and failed attempts remain unchanged, including the preceding metadata-harness failure, earlier legacy error-recovery output, aggregate-prefix OOM/sequencing qualification, statement-count correction, evidence-writer-label correction and additive disk precision correction. UUID logs are authoritative; semantic-label logs are convenience copies.

The complete recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives chunk hashes and the whole-file reconstruction hash; concatenate bytes in manifest order without added headers or separators. evidence-sha256.json seals every checkpoint file except itself.

reconcile.py rewrites current derived evidence/chunks without running Lean/checker and checks historical manifests without modifying them. Entry points: legacy_compare.py; run.py pilot/build/audit/replay; reconcile.py. Publication reconciliation runs no compiler/checker. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal process/lock/resource and repository-wide CI observations are saved. Paused for independent review; no other target is started.

Minimum observed cgroup headroom: 8258617344 bytes; minimum system MemAvailable: 17444782080 bytes.

Current checkpoint observed free disk: initially 17.47 GiB (18757038080 bytes), terminal 17.38 GiB (18666033152 bytes).
