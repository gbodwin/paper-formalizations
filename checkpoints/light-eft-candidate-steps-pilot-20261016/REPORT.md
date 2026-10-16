# StoredCandidateDrawLookup.steps total-recursor pilot

Tested source: `a8f7c3704db0afcfdf21762873f3c86a7dba605b`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredCandidateDrawLookup.steps._unsafe_rec` disappears: **40 → 39 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **78 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other repair target is started.

## Accepted baseline, capacity and historical preservation

The parent independently accepted source `8723e2833692780b0fc5de7096be0fb50d19dcbc` and evidence `8baaf6db300c44614e5a6f5204066ee64736286f` as a bounded incremental repair. Review was finished before execution. This records committed source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

Initial tracked state was clean at the accepted evidence commit. No Lean/Lake/checker was active and the universal lock was free. Approximately 20 GiB workspace disk was available; the memory limit was 16 GiB with about 6.4 GiB used. The worker rehashed all 486 accepted live source/object bindings and all 858 entries of the parent manifest. The affected closure was independently rederived from imports: 17 modules, with 469 unaffected objects. Initial capacity and process observations and every invocation's persisted preflight are preserved.

All historical checkpoint trees remain unchanged, including prior failed attempts, Controller's 494-preflight/495-receipt qualification, aggregate-prefix OOM/sequencing violation, theorem-count correction, evidence-writer-label correction and prior interruption reconciliation. No deleted/canceled ChatGPT workspace is accessed or recreated. No website, other paper or unrelated endpoint is changed.

## Exact arbitrary-input semantics

`steps` is replaced with explicit total `List.rec`, using base 1 and the original `StoredEdges.same key r.1` conditional. A match returns 1; a miss returns 1 plus the tail result. The nil and cons equations are proved by `rfl`. No key range, sortedness, distinctness, graph-validity or payload-validity premise is added.

`LegacyEquivalence.lean` imports the exact hash-bound accepted implementation and proves equality for every natural endpoint pair and every original Bank. The replacement body is byte-identical to production. Induction and congrArg use **no axioms**. All legacy object bindings, before-source hash, replacement body hash and comparison object hash are recorded. The first successful equality invocation is retained; after a proof-only source repair, a second successful invocation binds the identical replacement body to the final full-source hash. Both UUID snapshots remain available.

The equality preserves the terminal step for an empty or exhausted bank, first-match position, reversed-key matching, duplicate-key priority, and complete independence from payload contents. An empty first matching payload still stops the counter. Loops and arbitrarily large natural endpoints are permitted. Nested banks and draw lists may contain empty lists, duplicate keys, loops and repeated/reversed edges without changing the count semantics. This preserves the defined step count; it is not a new physical-runtime claim about recursor evaluation.

Twenty exact-count fixtures cover nil, first/second/last matches, reversed keys, duplicate priority, absent keys, empty first payloads, unrelated prefixes/suffixes, loops, endpoints of magnitude 10^20, rich nested payloads and 64-element prefixes both with and without a final match. Universal nil/cons examples and metadata checks establish safe, total, computable status, explicit List.rec, no self-reference and no partial companion.

## Source scope

Only `StoredCandidateDrawLookup.lean` changes in production Lean source. The entire prefix before steps, including accepted value and its two equation theorems, remains byte-identical. The implementation replacement adds two steps equations. All four pre-existing theorem statements are unchanged. lookup_trace remains byte-identical. In steps_le, exactly one simp argument changes from steps to steps_cons to retain the named tail in the induction hypothesis. No hypothesis or bound changes.

All other 485 closure source files remain byte-identical. In particular the entire `StoredCandidateDrawEncoding.lean` file, including both accepted typed implementations and their proof/equation statements, is unchanged. The preservation report records its hash. No warning suppression, blanket noncomputable conversion, alternate runtime or shim occurs.

## Complete affected build and exhaustive audit

All 17 affected modules, including the aggregate, receive fresh strict compilation. The other 469 objects retain individually verified accepted source, direct-import and object hashes. All affected states were removed before execution, so equal intermediate object bytes cannot skip required compilation. The evidence writer independently rederives imports and the closure again. Inherited receipt history is not counted as fresh execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and its binaries remain unchanged. All nine dependency revisions are checked before every runner invocation, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Toolchain, manifest and unchanged supervisor hashes are recorded and reconciled. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build or dependency change occurs.

The actual-owner audit and official resolver are unchanged apart from output-directory substitution. All project owners, recursive types/bodies, opaque values, inductive families and recursor rules remain covered. No generated name, remaining partial or violation is filtered, exempted or allowlisted.

Fresh audit: 9196 actual-owner roots, 60615 recursive constants, 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only propext, Classical.choice and Quot.sound appear as axioms in the complete closure. Exactly the target partial companion disappears; all other 39 partial roots remain unchanged. The strict audit exits 1 with 78 root/recursive findings. Full generated-name and actual-owner changes are recorded in owner-inventory-delta.json. This is a failing strict gate, not final acceptance.

## Authorized singleton replay and execution evidence

The official resolver selects exactly one object/module for `LightEFTSpanners.StoredCandidateDrawLookup`; the unchanged supervisor repeats singleton resolution while holding the universal lock. `leanchecker -v LightEFTSpanners.StoredCandidateDrawLookup` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay LEAN_PATH contains isolated current outputs, pinned package caches and the official toolchain, without historical project fallback. Singleton replay does not discharge the remaining partials; clean final exact-source validation remains required.

24 unique source-bound receipts and persisted preflights contain 516 submitted-source entries. They retain exact argv/options, source snapshots/hashes, lock inode, child PIDs, UTC/monotonic timing, exit status and reaping. Reconciliation verifies one lock inode, non-overlap, every snapshot and all children reaped. Concurrency is one. Zero anchored warning headers occur; hints and option names are not counted as warnings.

Two nonzero invocations are preserved in full. The initial module compile failed when omega treated the expanded steps recursor and the named induction-hypothesis tail as independent expressions. The single cons-equation simp substitution repairs that proof without changing its statement; this is not a mathematical counterexample. The other nonzero invocation is the unchanged strict audit rejecting the remaining 39 partial roots. All failed sources and raw diagnostics remain in authoritative UUID directories; semantic-label logs are convenience copies. Both successful legacy proof invocations are also retained.

`reconcile.py` is explicitly an evidence writer, not filesystem-read-only: it regenerates current derived evidence and audit chunks without invoking Lean/checker. Historical manifests are verified without modifying those directories. Checks cover source/object/import bindings, rederived closure, accepted value and typed source preservation, exact proof change, full recursive closure, one-companion delta, singleton replay, all receipts and historical preservation.

The full recursive TSV is retained with 207 ordered row-aligned chunks and reconstruction hash in `audit-export/manifest.json`. Concatenate bytes in manifest order without extra headers or separators. The evidence manifest seals all checkpoint files except itself.

Entry points: `python checkpoints/light-eft-candidate-steps-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-candidate-steps-pilot-20261016/run.py pilot`, `build`, `audit`, `replay`; and noncompiling writer `python checkpoints/light-eft-candidate-steps-pilot-20261016/reconcile.py`. Every compiler/checker invocation uses the unchanged universal exclusive supervisor, persisted preflights and source-bound receipts.

Publication uses additive source/evidence commits with `[skip ci]` after checking the existing remote branch. Terminal observations record no compiler/checker, the lock free, capacity and repository CI statuses. The worker stops for sequential independent review.
