# StoredOriginalWeightLookup.steps total-recursor pilot

Tested source: `89fa2461b4d11af3bd99fdbdc3fb4f44c1e9917b`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredOriginalWeightLookup.steps._unsafe_rec` disappears: **39 → 38 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **76 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other repair target is started.

## Accepted baseline, capacity and historical preservation

The parent independently accepted source `a8f7c3704db0afcfdf21762873f3c86a7dba605b` and evidence `5af2b165edb6d4ef698e52d599fc693f0813b06e` as a bounded incremental repair. Review was finished before execution. This records committed source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

Initial tracked state was clean at the accepted evidence commit. No Lean/Lake/checker was active and the universal lock was free. Approximately 19 GiB workspace disk was available; the memory limit was 16 GiB with about 6.6 GiB used. The worker rehashed all 486 accepted live source/object bindings and all 861 entries of the parent manifest. The affected closure was independently rederived from imports: 41 modules, with 445 unaffected objects. Initial capacity and process observations and every invocation's persisted preflight are preserved. Before each compiler/checker call, MemoryAdmission.py separately requires at least 4 GiB of cgroup headroom and 4 GiB of system MemAvailable; each individual observation is saved in memory-admissions.jsonl and reconciled with the invocation receipts. This is observed headroom, not a memory reservation or a claim that the supervisor disk gate checks memory. The original exclusive supervisor remains unchanged. Across all 47 invocations, the lowest observed cgroup headroom was 9837113344 bytes (about 9.16 GiB), and lowest system MemAvailable was 17607684096 bytes. See memory-admission-summary.json.

All historical checkpoint trees remain unchanged, including prior failed attempts, Controller's 494-preflight/495-receipt qualification, aggregate-prefix OOM/sequencing violation, theorem-count correction, evidence-writer-label correction and prior interruption reconciliation. No deleted/canceled ChatGPT workspace is accessed or recreated. No website, other paper or unrelated endpoint is changed.

The parent reported an environment-disconnected event at 18:00 UTC. The live reconciliation at 2026-10-16T18:01:14.663404+00:00 succeeded in the existing workspace: no active compiler/checker, free common lock, all 486 live source/object bindings reverified and all 47 children reaped. Compilation, audit and replay had already completed and the source commit was preserved. No process was restarted or duplicated; no user action was required. See evidence/interruption-reconciliation.json.

## Exact arbitrary-input semantics

`steps` is replaced with explicit total `List.rec`, using base 1 and the original `StoredEdges.same key r.1` conditional. A match returns 1; a miss returns 1 plus the tail result. The nil and cons equations are proved by `rfl`. No key range, sortedness, distinctness, graph-validity or payload-validity premise is added.

`LegacyEquivalence.lean` imports the exact hash-bound accepted implementation and proves equality for every natural endpoint pair and every original rational-valued Bank. The replacement body is byte-identical to production. Induction and congrArg use **no axioms**. All legacy object bindings, before-source hash, replacement body hash and comparison object hash are recorded. The first successful equality invocation is retained; after a proof-only source repair, a second successful invocation binds the identical replacement body to the final full-source hash. Both UUID snapshots remain available.

The equality preserves the terminal step for an empty or exhausted bank, first-match position, reversed-key matching, duplicate-key priority, and complete independence from payload contents. A zero, negative or fractional first matching payload still stops the counter. Loops and arbitrarily large natural endpoints are permitted. Rational values are unused by the counter and remain fully arbitrary; no nonnegativity, nonzero or integrality restriction is added. This preserves the defined step count; it is not a new physical-runtime claim about recursor evaluation.

Twenty exact-count fixtures cover nil, first/second/last matches, reversed keys, duplicate priority, absent keys, zero first payloads, unrelated prefixes/suffixes, loops, endpoints of magnitude 10^20, arbitrary signed rational payloads and 64-element prefixes both with and without a final match. Universal nil/cons examples and metadata checks establish safe, total, computable status, explicit List.rec, no self-reference and no partial companion.

## Source scope

Only `StoredOriginalWeightLookup.lean` changes in production Lean source. The entire prefix before steps, including the sibling value, transition, State and Bank definitions, remains byte-identical. The implementation replacement adds two steps equations. Both pre-existing theorem statements are unchanged. lookup_trace remains byte-identical. In steps_le, exactly one simp argument changes from steps to steps_cons to retain the named tail in the induction hypothesis. No hypothesis or bound changes.

All other 485 closure source files remain byte-identical. All sibling value and weight definitions and their encodings remain unchanged, as do the accepted candidate value/steps and typed implementations. Their source hashes are included in the full closure provenance. No warning suppression, blanket noncomputable conversion, alternate runtime or shim occurs.

## Complete affected build and exhaustive audit

All 41 affected modules, including the aggregate, receive fresh strict compilation. The other 445 objects retain individually verified accepted source, direct-import and object hashes. All affected states were removed before execution, so equal intermediate object bytes cannot skip required compilation. The evidence writer independently rederives imports and the closure again. Inherited receipt history is not counted as fresh execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and its binaries remain unchanged. All nine dependency revisions are checked before every runner invocation, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Toolchain, manifest and unchanged supervisor hashes are recorded and reconciled. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build or dependency change occurs.

The actual-owner audit and official resolver are unchanged apart from output-directory substitution. All project owners, recursive types/bodies, opaque values, inductive families and recursor rules remain covered. No generated name, remaining partial or violation is filtered, exempted or allowlisted.

Fresh audit: 9193 actual-owner roots, 60612 recursive constants, 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only propext, Classical.choice and Quot.sound appear as axioms in the complete closure. Exactly the target partial companion disappears; all other 38 partial roots remain unchanged. The strict audit exits 1 with 76 root/recursive findings. Full generated-name and actual-owner changes are recorded in owner-inventory-delta.json. This is a failing strict gate, not final acceptance.

## Authorized singleton replay and execution evidence

The official resolver selects exactly one object/module for `LightEFTSpanners.StoredOriginalWeightLookup`; the unchanged supervisor repeats singleton resolution while holding the universal lock. `leanchecker -v LightEFTSpanners.StoredOriginalWeightLookup` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay LEAN_PATH contains isolated current outputs, pinned package caches and the official toolchain, without historical project fallback. Singleton replay does not discharge the remaining partials; clean final exact-source validation remains required.

47 unique source-bound receipts and persisted preflights contain 539 submitted-source entries. They retain exact argv/options, source snapshots/hashes, lock inode, child PIDs, UTC/monotonic timing, exit status and reaping. Reconciliation verifies one lock inode, non-overlap, every snapshot and all children reaped. Concurrency is one. Zero anchored warning headers occur; hints and option names are not counted as warnings.

The only nonzero invocation is the unchanged strict audit rejecting the remaining 38 partial roots. Before compilation, the single cons-equation simp substitution in steps_le was applied based on the already accepted analogous counter repair. No compile or fixture attempt failed in this checkpoint, and no mathematical counterexample is claimed. All failed sources and raw diagnostics remain in authoritative UUID directories; semantic-label logs are convenience copies. Both successful legacy proof invocations are also retained.

`reconcile.py` is explicitly an evidence writer, not filesystem-read-only: it regenerates current derived evidence and audit chunks without invoking Lean/checker. Historical manifests are verified without modifying those directories. Checks cover source/object/import bindings, rederived closure, sibling definitions and existing hypotheses preservation, exact proof change, full recursive closure, one-companion delta, singleton replay, all receipts and historical preservation.

The full recursive TSV is retained with 207 ordered row-aligned chunks and reconstruction hash in `audit-export/manifest.json`. Concatenate bytes in manifest order without extra headers or separators. The evidence manifest seals all checkpoint files except itself.

Entry points: `python checkpoints/light-eft-weight-steps-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-weight-steps-pilot-20261016/run.py pilot`, `build`, `audit`, `replay`; and noncompiling writer `python checkpoints/light-eft-weight-steps-pilot-20261016/reconcile.py`. Every compiler/checker invocation uses the unchanged universal exclusive supervisor, persisted preflights and source-bound receipts.

Publication uses additive source/evidence commits with `[skip ci]` after checking the existing remote branch. Terminal observations record no compiler/checker, the lock free, capacity and repository CI statuses. The worker stops for sequential independent review.
