# StoredDrawLookup.value total-recursor pilot

Tested source: `e5eeb9ae503b4ab31af5593f898f6cf43b09a2b0`. Branch: `light-eft-spanners-checkpoints`. Exact source/object binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredDrawLookup.value._unsafe_rec` disappears: **30 → 29 partial roots**, none added. The unchanged exhaustive strict gate still fails with **58 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Baseline and admission

The parent accepted source `6c020d40a958aff19d7db7ec3592df3d107f997b` and evidence `421cddc17ccddb5bd8383db5aec6b325cd8c375f`. Review had finished before this work. This records source/log/hash reconciliation, not fresh reviewer execution or live-object inspection.

Connection and accepted tracked state were verified before admission. All 1,422 parent-manifest entries and all 486 live source/object bindings matched. The actual value declaration and accepted typedValue sibling were inspected. No Lean/Lake/checker was active, the common lock was free, and memory met admission thresholds. Initial and terminal resource bytes and UTC observations are retained; disk GiB uses 2^30 bytes. No canceled workspace, other paper or website was accessed or changed.

Every invocation requires at least 4 GiB cgroup headroom and 4 GiB system MemAvailable, recorded individually and reconciled with its receipt. This is separate from the supervisor disk gate and is not a memory reservation or peak-use guarantee. MemoryAdmission.py and the common exclusive supervisor are unchanged. There is no parallel worker or concurrent review.

## Complete first-match payload equality

The replacement follows accepted typedValue's total List.rec pattern. The empty bank returns []; each record returns its entire payload if its key matches, otherwise the recursive tail result. The two equations are proved by rfl. An empty matching payload remains a successful first match and blocks all later duplicates. The code never searches for a nonempty match, merges payloads, reorders inner draws/edges, normalizes orientations or removes duplicates.

LegacyEquivalence.lean imports exact hash-bound accepted objects and proves equality of the complete nested payload for every natural key and arbitrary bank. Induction applies congrArg to the original conditional; the replacement body is identical to production. The successful theorem is axiom-free. No uniqueness, validity, key-range, nonempty-payload or payload-shape premise is introduced.

Twenty fixtures compare full nested lists, covering absent keys, duplicate-key first-match priority in both orders, an empty first payload before a later nonempty match, empty inner draws distinguished from an empty outer payload, skipped nonmatching records, loops, oriented/repeated edges, preserved inner/outer order, very large keys and edge endpoints, and longer banks. Metadata checks verify safe, total, computable, explicit List.rec, no self-reference and no partial companion. Semantic equality is not a physical-runtime claim about the recursor.

Two production files change. StoredDrawLookup.lean changes only the value definition, adds two equations and changes two simplification arguments in lookup_trace from value to value_cons. State, transition, Bank and steps are unchanged; both pre-existing theorem headers and the steps_le body are unchanged. StoredDrawLookupEncoding.lean changes one simplification argument list in value_encoded to use value_cons and the existing typedValue_cons. Every definition there, including accepted typedValue and typedInputs, remains byte-identical; all five theorem headers are unchanged. These proof-interface changes were made before compilation. All other 484 closure source files remain unchanged.

## Complete affected validation

The source-import closure is independently recomputed: 74 fresh affected strict builds, including aggregate compilation, and 412 inherited objects with accepted source, direct-import and object hashes. Every affected state entry was removed before rebuilding so equal intermediate outputs cannot bypass compilation. Historical receipts are not counted as fresh execution.

Official Lean 4.34.0 commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and all nine dependency revisions remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Runners verify all revisions. Exact executable, manifest and supervisor hashes are retained. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, weakening, alternate runtime or blanket noncomputable change occurs.

The exhaustive actual-owner/recursive audit is unchanged except output-directory substitution. It covers 9140 project roots, 60559 recursive constants and 48 opaque bodies, including generated declarations, recursive types/bodies, inductive families and recursor rules. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. No unsafe project roots or aggregate-owned declarations occur. Exactly the value companion disappears; all other 29 partial roots remain. The strict audit exits 1 with 58 root/recursive findings. No violation is filtered, exempted or allowlisted.

Official resolution selects exactly LightEFTSpanners.StoredDrawLookup; the supervisor repeats resolution under the lock. `leanchecker -v LightEFTSpanners.StoredDrawLookup` passes with one replay line. No aggregate-prefix replay occurs. Audit/replay use isolated current outputs and pinned packages without historical project fallback. Legacy equality uses separately hash-bound accepted objects. Singleton replay does not discharge other partials or replace required clean final exact-source validation.

## Receipts, diagnostics and preservation

79 unique source-bound receipts contain 569 submitted-source entries and individual persisted preflights/memory admissions. Each invocation records exact argv/options, snapshots/hashes, lock identity, child PID, UTC/monotonic timing, exit and reaping. Reconciliation checks hashes, UUID uniqueness, one lock inode, strict non-overlap, all children reaped, complete affected closure, inherited provenance and historical preservation. Zero anchored warning headers occur; hints and option names are not warnings.

The only nonzero invocation was the unchanged exhaustive audit rejecting remaining partial roots, UUID 661bc78c17014874b9c3676642924a77. No legacy proof, production compile or fixture failed. The full audit diagnostic and submitted snapshots are preserved.

All historical checkpoint trees, raw failures and qualifications remain unchanged, including prior legacy recovery output, metadata-harness failure, aggregate-prefix OOM/sequencing qualification, statement-count correction, evidence-writer-label correction and disk precision correction. UUID raw logs are authoritative; semantic-label logs are convenience copies.

The full recursive TSV and 207 ordered row-aligned chunks are retained. audit-export/manifest.json gives chunk hashes and the whole-file reconstruction hash; concatenate bytes in order without additional headers or separators. evidence-sha256.json seals every checkpoint file except itself.

reconcile.py regenerates current derived evidence/chunks without running Lean/checker and checks historical manifests without modifying them. Entry points: legacy_compare.py; run.py pilot/build/audit/replay; reconcile.py. Publication reconciliation runs no compiler/checker. Additive source/evidence commits use [skip ci] and normal push after remote-state checks. Terminal process/lock/resource and repository-wide CI observations are saved. Paused for independent review; no other target is started.

Minimum observed cgroup headroom: 8038580224 bytes; minimum system MemAvailable: 17489510400 bytes.

Current checkpoint observed free disk: initially 17.27 GiB (18548006912 bytes), terminal 17.19 GiB (18458411008 bytes).
