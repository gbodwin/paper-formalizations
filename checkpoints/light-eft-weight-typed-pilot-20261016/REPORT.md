# StoredOriginalWeightLookup.weight total-recursor pilot

Tested source: `5477df1f6fadd5d1bb10ecda9862e2ec59b155ea`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredOriginalWeightLookup.weight._unsafe_rec` disappears: **37 → 36 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **72 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other target is started.

## Accepted baseline, capacity and preservation

The parent independently accepted source `23c20b1c58bb24bc53419819ae755f82b7f71cd8` and evidence `3a4321ef8255daafbae445d56b63e54516e22df7` as a bounded incremental repair. Review was finished before execution. This records committed source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

Initial tracked state was clean at the accepted evidence commit. No Lean/Lake/checker was active and the universal lock was free. Approximately 19 GiB disk was available; the cgroup memory limit was 16 GiB with about 7.0 GiB used. The worker rehashed all 486 accepted live source/object bindings and all 979 parent-manifest entries. The independently rederived source-import closure contains 40 affected modules and 446 unaffected modules.

Every compiler/checker invocation separately requires at least 4 GiB of cgroup headroom and 4 GiB system MemAvailable before admission. Individual observations in memory-admissions.jsonl are reconciled with execution receipts, with minima in memory-admission-summary.json. This is observed available memory, not a memory reservation or a claim that the disk gate checks memory. MemoryAdmission.py and the universal exclusive supervisor are unchanged from the accepted checkpoint. Individual supervisor preflights retain disk/process/memory observations. Across all 45 invocations, minimum cgroup headroom was 9399324672 bytes (about 8.75 GiB), and minimum system MemAvailable was 17549520896 bytes.

All historical checkpoint trees, failed attempts and qualifications remain unchanged, including the Controller 494-preflight/495-receipt gap, historical aggregate-prefix OOM/sequencing violation, theorem-count correction, evidence-writer-label correction and interruption records. No deleted/canceled ChatGPT workspace is accessed or recreated. No website or unrelated paper is changed.

## Universal typed rational-payload semantics

The typed weight recursion becomes explicit total `List.rec`, with base rational zero and the original `e=s(r.1.1,r.1.2)` Sym2 equality test. A match returns the complete rational payload r.2; otherwise the tail result is returned. Explicit nil/cons equations are proved by `rfl`.

`LegacyEquivalence.lean` imports the exact hash-bound accepted implementation and proves equality for every n, every `e : Sym2 (Fin n)` and every `TypedBank n`. Its replacement body is byte-identical to production. Induction and congrArg preserve the original conditional. The theorem depends only on **propext and Quot.sound**, as printed by Lean; no axiom or mathematical hypothesis is added. Before-source, replacement body, all legacy object hashes and comparison-object hash are preserved. The comparison intentionally uses accepted legacy objects; audit/replay use isolated current outputs.

Rational payloads remain arbitrary, including zero, negative values, fractions and large magnitudes. The first matching entry wins, including a zero first match before a nonzero match and a negative first match before a positive one. Sym2 equality preserves reversed-pair matching and duplicate priority. An absent key returns zero. No sortedness, uniqueness, positivity, nonnegativity or integrality premise is introduced. Endpoints retain the original Fin n bound, with arbitrary n and loops permitted. For n=0 no query key exists; the original impossible-input boundary is explicitly proved rather than presenting an impossible executable query. This is semantic equality, not a physical-runtime claim about recursor evaluation.

Twenty exact-payload fixtures compare complete rational results: empty/missing banks, signed and fractional first matches, zero before later nonzero matches, duplicate/reversed keys, unrelated prefixes/suffixes, singleton loops, large rational numerators and 64-element prefixes with and without a final match. Separate universal nil/cons examples and an n=0 impossibility proof compile. Metadata checks verify safety, totality, computability, explicit List.rec, no self-reference and no partial companion.

## Source scope

Only `StoredOriginalWeightEncoding.lean` changes in production Lean source. TypedBank and encode remain byte-identical. The weight body is replaced and two equation theorems are added. Both pre-existing theorem statements and bodies, value_encoded and weight_nonnegative, remain byte-identical. In particular weight_nonnegative retains exactly its original nonnegativity hypothesis, which is not imposed on the universal equality theorem.

All other 485 closure source files remain byte-identical. The whole `StoredOriginalWeightLookup.lean` file is unchanged, including repaired value and steps, their equations, lookup_trace and steps_le. lookup_trace is a theorem, not a partial target. Its preservation hash is saved in sibling-preservation.json. There is no supporting proof edit in this checkpoint.

## Complete affected rebuild and audit

All 40 affected modules, including the aggregate, receive fresh strict compilation. The remaining 446 objects retain individually verified accepted source, direct-import and object hashes. Every affected state was removed before building so equal intermediate object bytes cannot skip required compilation. The evidence writer rederives the import closure from current source. Inherited historical receipts are not counted as fresh execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, remains unchanged. All nine dependency revisions are checked before each runner invocation, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Exact toolchain, manifest and supervisor hashes are recorded and reconciled. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, dependency change, warning suppression, blanket noncomputable conversion, shim or alternate runtime occurs.

The complete actual-owner audit and official resolver are unchanged apart from output-directory substitution. All project owners, recursive types/bodies, opaque values, inductive families and recursor rules remain covered. No generated name, remaining partial or violation is filtered, exempted or allowlisted.

Fresh audit: 9179 actual-owner roots, 60598 recursive constants and 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only propext, Classical.choice and Quot.sound appear as axioms in the full closure. Exactly the target partial companion disappears; all other 36 partial roots remain unchanged. Strict audit exits 1 with 72 root/recursive findings. Full generated-name and owner changes appear in owner-inventory-delta.json. This is a failing strict gate, not final acceptance.

## Singleton replay, memory admission and raw evidence

The official resolver selects exactly one object/module for `LightEFTSpanners.StoredOriginalWeightEncoding`; the supervisor repeats singleton resolution under the universal lock. `leanchecker -v LightEFTSpanners.StoredOriginalWeightEncoding` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay LEAN_PATH contains isolated current project outputs, pinned packages and official toolchain without historical project fallback. Singleton replay does not discharge the remaining partials; clean final exact-source validation remains required.

45 unique source-bound receipts have both persisted supervisor preflights and individual memory-admission observations. They contain 535 submitted-source entries, exact argv/options, snapshots/hashes, lock inode, child PIDs, UTC/monotonic times, exits and reaping. Reconciliation verifies all snapshots, one lock inode, non-overlap and all children reaped. Compiler/checker concurrency is one. Zero anchored warning headers occur; hints and option names are not counted as warnings.

The only nonzero invocation is the unchanged strict audit rejecting the remaining 36 partial roots. No compiler or fixture attempt failed, and no mathematical counterexample is claimed. The raw audit diagnostic and submitted source snapshots are preserved. All historical failed attempts remain unchanged.

UUID directories preserve authoritative raw diagnostics and exact submitted sources; semantic-label logs are convenience copies. All historical failed attempts remain unchanged. `reconcile.py` is explicitly an evidence writer: it regenerates current derived evidence and chunks without invoking Lean/checker. It verifies historical manifests without modifying them. Its checks cover source/object/import bindings, exact closure, sibling preservation, unchanged hypotheses, full recursive audit, exact one-companion delta, singleton replay, memory admissions, receipts and historical preservation.

The complete recursive TSV is retained with 207 ordered row-aligned chunks and reconstruction hash in `audit-export/manifest.json`. Concatenate chunk bytes in manifest order without extra headers or separators. The evidence manifest seals all checkpoint files except itself.

Entry points: `python checkpoints/light-eft-weight-typed-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-weight-typed-pilot-20261016/run.py pilot`, `build`, `audit`, `replay`; and the noncompiling evidence writer `python checkpoints/light-eft-weight-typed-pilot-20261016/reconcile.py`. All compiler/checker invocations use the unchanged universal supervisor and memory admission helper.

Publication uses additive source/evidence commits with `[skip ci]` after remote-state checks. Terminal observations record no compiler/checker, a free common lock, resource capacity and repository CI statuses. The worker stops for sequential independent review.
