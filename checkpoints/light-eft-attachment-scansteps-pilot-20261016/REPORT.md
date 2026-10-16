# StoredForestDrawAttachment.scanSteps total-recursor pilot

Tested source: `dde0905c34ad4c32fd0676014ac1af4ca4abd878`. Branch: `light-eft-spanners-checkpoints`. Exact source/object binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredForestDrawAttachment.scanSteps._unsafe_rec` disappears: **27 → 26 partial roots**, none added. The unchanged exhaustive strict gate still fails with **52 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Baseline and admission

The parent accepted source `143d1192bb347426e13f33f88a817eb945f6c554` and evidence `d4f5b7d567659335061fa09120d912aec047bc57`; review had finished. This records source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

Live commands verified the connection and clean accepted tracked state before compiler admission. All 1,177 parent-manifest entries and all 486 live source/object bindings matched. The actual scanSteps declaration, key formula and bound consumer were inspected. No Lean/Lake/checker was active, the common lock was free, and resources met admission thresholds. Initial/terminal bytes and UTC observations are retained; GiB uses 2^30 bytes. No canceled workspace, other paper or website was accessed or changed.

Each invocation has an individual persisted memory admission requiring at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, separate from the supervisor disk gate. These observations are not reservations or peak-use guarantees. MemoryAdmission.py and the exclusive supervisor remain unchanged. No parallel worker or concurrent review was used.

## Unrestricted full-count equality

The replacement is explicit total List.rec with base one and cons function `StoredDrawLookup.steps (key n r) bank + 2 + rest`. The two equations are proved by rfl. The base counts the empty-record transition to reversal; the two extra cons transitions enter lookup and attach the returned payload. The full lookup count, including misses and empty successful payloads, is retained. This is the scan budget, not the additional reversal budget supplied by unchanged sibling steps.

LegacyEquivalence.lean imports exact hash-bound accepted objects and proves equality of the complete natural result for arbitrary n, bank and record list. Induction applies congrArg to addition of the exact lookup-plus-two term. The replacement body is identical to production. The successful theorem is axiom-free. No root-range, valid-component, unique-key, nonempty-payload, record-validity or bank-validity premise is introduced.

Twenty exact-count fixtures cover empty inputs, empty banks, first/later/missing keys, multiple/repeated/reordered records, first-match empty payloads before duplicates, nonmatching prefixes, arbitrary record contents, n=0 label collisions, huge natural labels, long banks and long record lists. The full count includes every lookup, both transition charges and the final scan base. Metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. Formal count equality is not a physical-runtime claim about recursor evaluation.

Two production files change. StoredForestDrawAttachment.lean changes only scanSteps and adds two equations. The complete prefix, including Record, State, key, attached, transition and value, remains byte-identical. Both existing theorem headers retain their hypotheses; lookup_lift is unchanged and scan_trace changes one simplification argument to scanSteps_cons. StoredForestDrawAttachmentBound.lean changes two scanSteps_le simplification arguments to scanSteps_nil/scanSteps_cons. All four existing headers, other proof bodies and steps/bound definitions remain unchanged. These anticipated proof-interface repairs were made before compilation. All other 484 closure source files are unchanged.

## Complete sequential validation

The independently recomputed source-import closure contains 73 affected strict builds, including aggregate compilation, and 413 inherited objects retaining accepted source, direct-import and object hashes. Every affected state entry was removed before rebuilding so equal intermediate outputs cannot bypass compilation. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency revisions remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions; exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable changes occur.

The exhaustive audit is unchanged except output-directory substitution. It covers 9116 actual-owner project roots, 60535 recursive constants and 48 opaque bodies, including generated declarations, recursive types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. No unsafe project roots or aggregate-owned declarations occur. Exactly the scanSteps companion disappears; all other 26 partial roots remain. The audit exits 1 with 52 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official resolution selects exactly LightEFTSpanners.StoredForestDrawAttachment, and the supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredForestDrawAttachment` passes with one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages without historical project fallback. Legacy equality uses separately hash-bound accepted objects. Singleton replay does not discharge remaining partials or replace clean final exact-source validation.

## Evidence and preservation

78 unique source-bound receipts contain 568 submitted-source entries and individual persisted preflights/memory admissions. Each records exact argv/options, snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation verifies hashes, UUID uniqueness, one lock inode, strict non-overlap, all children reaped, complete closure, inherited provenance and historical preservation. Zero anchored warning headers occur; hints and option names are not warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID 64be739a8f79461eaff6d2d49d427a03. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees, raw failures and qualifications remain unchanged, including the preceding forest encoding failure, earlier legacy recovery output, metadata-harness failure, aggregate-prefix OOM/sequencing qualification, statement-count correction, evidence-writer-label correction and disk precision correction. UUID logs are authoritative; semantic-label logs are convenience copies.

The full recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives chunk hashes and whole-file reconstruction hash; concatenate bytes in order without added headers or separators. evidence-sha256.json seals every checkpoint file except itself.

reconcile.py rewrites current derived evidence/chunks without running Lean/checker and checks historical manifests without modifying them. Entry points: legacy_compare.py; run.py pilot/build/audit/replay; reconcile.py. Publication reconciliation runs no compiler/checker. Additive source/evidence commits use [skip ci], with normal push after remote-state checks. Terminal process/lock/resources and repository-wide CI observations are saved. Paused for independent review; no other target is started.

Minimum observed cgroup headroom: 7382917120 bytes; minimum system MemAvailable: 17381314560 bytes.

Current checkpoint observed free disk: initially 16.70 GiB (17927831552 bytes), terminal 16.61 GiB (17837961216 bytes).
