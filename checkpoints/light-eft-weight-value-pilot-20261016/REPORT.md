# StoredOriginalWeightLookup.value total-recursor pilot

Tested source: `23c20b1c58bb24bc53419819ae755f82b7f71cd8`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredOriginalWeightLookup.value._unsafe_rec` disappears: **38 → 37 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **74 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other target is started.

## Accepted baseline, capacity and preservation

The parent independently accepted source `89fa2461b4d11af3bd99fdbdc3fb4f44c1e9917b` and evidence `dbca872f0b1053fc1f6d86b8e3196df173ab2b75` as a bounded incremental repair. Review was finished before execution. This records committed source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

Initial tracked state was clean at the accepted evidence commit. No Lean/Lake/checker was active and the universal lock was free. Approximately 19 GiB disk was available; the cgroup memory limit was 16 GiB with about 6.8 GiB used. The worker rehashed all 486 accepted live source/object bindings and all 980 parent-manifest entries. The independently rederived source-import closure contains 41 affected modules and 445 unaffected modules.

Every compiler/checker invocation separately requires at least 4 GiB of cgroup headroom and 4 GiB system MemAvailable before admission. Individual observations in memory-admissions.jsonl are reconciled with execution receipts, with minima in memory-admission-summary.json. This is observed available memory, not a memory reservation or a claim that the disk gate checks memory. MemoryAdmission.py and the universal exclusive supervisor are unchanged from the accepted checkpoint. Individual supervisor preflights retain disk/process/memory observations. Across all 47 invocations, minimum cgroup headroom was 9616412672 bytes (about 8.96 GiB), and minimum system MemAvailable was 17590902784 bytes.

All historical checkpoint trees, failed attempts and qualifications remain unchanged, including the Controller 494-preflight/495-receipt gap, historical aggregate-prefix OOM/sequencing violation, theorem-count correction, evidence-writer-label correction and interruption records. No deleted/canceled ChatGPT workspace is accessed or recreated. No website or unrelated paper is changed.

## Universal rational-payload semantics

The value recursion becomes explicit total `List.rec`, with base rational zero and the original `StoredEdges.same key r.1` conditional. A match returns the entire rational payload r.2; otherwise it returns the tail result. Explicit nil/cons equations are proved by `rfl`.

`LegacyEquivalence.lean` imports the exact hash-bound accepted implementation and proves equality for every original natural endpoint pair and every rational-valued Bank. The replacement body is byte-identical to production. Induction and congrArg preserve the original conditional. The theorem depends only on **propext and Quot.sound**, as printed by Lean; no axiom or mathematical hypothesis is added. Before-source, replacement body, all legacy object hashes and comparison-object hash are preserved. The comparison intentionally uses accepted legacy objects; the new audit and replay use isolated current outputs.

Arbitrary rational payloads remain unrestricted, including zero, negative values, fractions and large magnitudes. The first matching entry wins, including a zero first match followed by a nonzero match, or a negative first match followed by a positive one. Reversed keys retain undirected matching, duplicate priority is unchanged, and absent keys return zero. Natural endpoints remain unbounded and loops are permitted. No sortedness, uniqueness, graph validity, positivity, nonnegativity, nonzero or integrality premise is introduced. This is value equivalence, not a physical-runtime claim about evaluating the recursor.

Twenty exact-payload fixtures compare complete rational results, covering empty and missing banks; positive, negative, zero and fractional first matches; duplicate/reversed keys; unrelated prefixes/suffixes; loops; endpoints of magnitude 10^20; large rational numerators; and 64-element prefixes with and without a final match. Universal nil/cons examples and metadata checks establish safe, total, computable status, explicit List.rec, no self-reference and no partial companion.

## Source scope

Two production Lean files change. In StoredOriginalWeightLookup.lean, only value is replaced and two explicit equation theorems are added. The entire prefix before value and suffix beginning at def steps remain byte-identical, including repaired steps, its equations, lookup_trace and steps_le. All four pre-existing theorem statements and bodies in this file are unchanged.

StoredOriginalWeightEncoding.lean changes one simp argument in value_encoded, from value to value_cons. TypedBank, encode, the typed weight definition, weight_nonnegative and both existing theorem statements remain unchanged. In particular the original nonnegativity hypothesis of weight_nonnegative is preserved and is not added to value equivalence. All other 484 closure source files are byte-identical.

## Complete affected rebuild and audit

All 41 affected modules, including the aggregate, receive fresh strict compilation. The remaining 445 objects retain individually verified accepted source, direct-import and object hashes. Every affected state was removed before building so equal intermediate object bytes cannot skip required compilation. The evidence writer rederives the import closure from current source. Inherited historical receipts are not counted as fresh execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, remains unchanged. All nine dependency revisions are checked before each runner invocation, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Exact toolchain, manifest and supervisor hashes are recorded and reconciled. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, dependency change, warning suppression, blanket noncomputable conversion, shim or alternate runtime occurs.

The complete actual-owner audit and official resolver are unchanged apart from output-directory substitution. All project owners, recursive types/bodies, opaque values, inductive families and recursor rules remain covered. No generated name, remaining partial or violation is filtered, exempted or allowlisted.

Fresh audit: 9186 actual-owner roots, 60605 recursive constants and 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only propext, Classical.choice and Quot.sound appear as axioms in the full closure. Exactly the target partial companion disappears; all other 37 partial roots remain unchanged. Strict audit exits 1 with 74 root/recursive findings. Full generated-name and owner changes appear in owner-inventory-delta.json. This is a failing strict gate, not final acceptance.

## Singleton replay, memory admission and raw evidence

The official resolver selects exactly one object/module for `LightEFTSpanners.StoredOriginalWeightLookup`; the supervisor repeats singleton resolution under the universal lock. `leanchecker -v LightEFTSpanners.StoredOriginalWeightLookup` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay LEAN_PATH contains isolated current project outputs, pinned packages and official toolchain without historical project fallback. Singleton replay does not discharge the remaining partials; clean final exact-source validation remains required.

47 unique source-bound receipts have both persisted supervisor preflights and individual memory-admission observations. They contain 537 submitted-source entries, exact argv/options, snapshots/hashes, lock inode, child PIDs, UTC/monotonic times, exits and reaping. Reconciliation verifies all snapshots, one lock inode, non-overlap and all children reaped. Compiler/checker concurrency is one. Zero anchored warning headers occur; hints and option names are not counted as warnings.

Two nonzero invocations are preserved. The initial encoding compile exposed a mismatch between the expanded value recursor and the named induction hypothesis, plus a strict unused-simp-argument diagnostic. The single value_cons substitution repairs the proof without changing its statement or the typed weight definition. This is a proof repair, not a mathematical counterexample. The other nonzero invocation is the unchanged strict audit rejecting the remaining 37 partial roots. All exact-payload fixtures pass.

UUID directories preserve authoritative raw diagnostics and exact submitted sources; semantic-label logs are convenience copies. All historical failed attempts remain unchanged. `reconcile.py` is explicitly an evidence writer: it regenerates current derived evidence and chunks without invoking Lean/checker. It verifies historical manifests without modifying them. Its checks cover source/object/import bindings, exact closure, sibling preservation, unchanged hypotheses, full recursive audit, exact one-companion delta, singleton replay, memory admissions, receipts and historical preservation.

The complete recursive TSV is retained with 207 ordered row-aligned chunks and reconstruction hash in `audit-export/manifest.json`. Concatenate chunk bytes in manifest order without extra headers or separators. The evidence manifest seals all checkpoint files except itself.

Entry points: `python checkpoints/light-eft-weight-value-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-weight-value-pilot-20261016/run.py pilot`, `build`, `audit`, `replay`; and the noncompiling evidence writer `python checkpoints/light-eft-weight-value-pilot-20261016/reconcile.py`. All compiler/checker invocations use the unchanged universal supervisor and memory admission helper.

Publication uses additive source/evidence commits with `[skip ci]` after remote-state checks. Terminal observations record no compiler/checker, a free common lock, resource capacity and repository CI statuses. The worker stops for sequential independent review.
