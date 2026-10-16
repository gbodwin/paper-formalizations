# StoredOriginalCandidateRecords.value total-recursor pilot

Tested source: `a047d25d17a9729aee544844d301353e5af4ada9`. Branch: `light-eft-spanners-checkpoints`. Source/object binding: `evidence/source-binding.json` and `source-object-provenance.json`.

This is a bounded incremental repair, awaiting independent review. Exactly `LightEFTSpanners.StoredOriginalCandidateRecords.value._unsafe_rec` disappears: **42 → 41 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **82 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other repair target is started.

## Accepted baseline, resources and preservation

The parent independently accepted source `3659611df7b31736793bbd547aa5b494f73b7cc5` and evidence `4a10cb9c2ea278bbce908ceeaa81e7b97e7d43fd` as an incremental repair. Review was finished before execution. This records committed source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

The initial tracked worktree was clean at the accepted evidence commit, with no active Lean/Lake/checker and the universal lock free. About 20 GiB workspace disk was free; memory limit was 16 GiB, usage about 6 GiB. The worker rehashed all 486 accepted live source/object bindings and all 1123 entries of the parent manifest. The independently rederived source-import closure has 16 affected modules and 470 unaffected modules. Capacity and process observations are saved before execution and in each invocation preflight.

All historical checkpoint trees remain unchanged. Earlier failed attempts, Controller's 494-preflight/495-receipt qualification, the historical aggregate-prefix OOM/sequencing violation, theorem-count correction and evidence-writer-label correction remain preserved. No deleted/canceled ChatGPT workspace is accessed or recreated. Work stays on Light EFT; no website or other paper is changed.

## Complete universal semantics

The original `value` equation compiler recursion is replaced with explicit total `List.rec`. The original `StoredEdges.contains x Q` filter and `StoredCandidateDrawLookup.value x bank` lookup expressions are unchanged. The tail result is returned for filtered candidates; otherwise the entire record containing the original oriented edge and full lookup payload is prepended. Explicit nil and cons equations are proved by `rfl`.

`LegacyEquivalence.lean` imports the exact hash-bound accepted implementation and proves equality of complete output record lists for arbitrary Q, bank and candidate lists. Its replacement body is byte-identical to production. Induction uses congrArg on the unchanged filter/record constructor. The equality theorem uses **no axioms**. Accepted legacy object hashes, before-source hash, replacement body hash and comparison-object hash are saved. The comparison deliberately uses preserved legacy objects; the new audit and replay use only the new isolated project outputs.

There is no bounded-endpoint, sortedness, forest, loop-free, distinct-edge, well-formed-bank or nonempty-payload premise. Endpoints are arbitrary natural numbers. Undirected filter membership removes all matching orientations; survivor records retain original orientation, duplicates and order. Lookup retains its existing first-match semantics, including duplicate/reversed keys and empty first matches. Nested bank keys, draw-list order, duplicate edges, reversed edges, loops and empty draws are preserved as full payloads.

Nineteen executable fixtures compare complete `StoredForestBank.Input` records using their existing structural equality. Expected records specify both edge and entire nested bank payload; checks are not limited to projections or lengths. Cases include empty lists, missing banks, removed and surviving loops, duplicate/reversed candidates and filter entries, unrelated filters, first-match duplicate/reversed bank keys, empty first payloads, ordered survivor concatenation, unrestricted nested payloads and endpoints of magnitude 10^20. Universal nil/cons checks and metadata checks verify safe, total, computable status, explicit List.rec, no self-reference and no partial companion.

## Narrow source changes

Only two production Lean files change. `StoredOriginalCandidateRecords.lean` replaces value and adds its two equation theorems; its state, transition, bound and both pre-existing theorem bodies/statements remain byte-identical. `StoredOriginalCandidateSupport.lean` changes one simp argument in value_length from value to value_cons. Its three existing theorem statements and all definitions remain unchanged. All other 484 closure source files are byte-identical.

The entire `StoredCandidateDrawEncoding.lean` file is byte-identical to the accepted source, including the accepted typed implementation, its equations and encoding theorem. `typed-implementation-preservation.json` records its hash. No theorem premise, mathematical coverage or runtime claim is strengthened or weakened.

## Build, exhaustive audit and authorized replay

All 16 affected modules, including the aggregate, receive fresh strict compilation. The remaining 470 objects retain verified accepted source, direct-import and object bindings. Inherited receipts are not counted as fresh execution. The closure is rederived from imports, and every affected state is removed before build so equal intermediate object bytes cannot skip required recompilation.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, remains unchanged. All nine dependencies are checked against lake-manifest.json before each runner invocation, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Toolchain, supervisor and manifest hashes are recorded and reconciled. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, dependency update, runtime shim or blanket noncomputable conversion occurs.

The exhaustive actual-owner audit and official resolver are unchanged apart from output-directory substitution. Audit coverage includes all project owners, recursive types/bodies, opaque values, inductive families and recursor rules, without filtering generated names, partial roots or remaining violations. Fresh audit reports 9206 actual-owner roots, 60625 recursive constants and 48 opaque bodies; zero unsafe project roots and zero aggregate-owned declarations. Only propext, Classical.choice and Quot.sound occur in the complete closure. Exactly one target partial companion is removed; the other 41 partial roots are unchanged. Exit 1 with 82 findings is preserved as a failing strict gate.

Official resolution verifies exactly one object/module for `LightEFTSpanners.StoredOriginalCandidateRecords`. The unchanged supervisor repeats singleton resolution under the universal lock. `leanchecker -v LightEFTSpanners.StoredOriginalCandidateRecords` passes with exactly one replay line. No aggregate-prefix replay occurs. Passing this individual replay does not discharge the remaining strict-audit failures. Audit/replay LEAN_PATH contains isolated new outputs, pinned dependency caches and the official toolchain, without historical project fallback. Validation is incremental; clean final validation remains required.

## Receipts, failures and readable exports

22 unique source-bound receipts and persisted preflights include 512 submitted-source entries. Exact argv/options, source snapshots and hashes, lock inode, child PIDs, UTC/monotonic timing, exit status and reaping are preserved. Reconciliation verifies non-overlap, one lock inode, all snapshots and all children reaped. Compiler/checker concurrency is one. Zero anchored warning headers occur; hints and option names are not counted as warnings.

Two nonzero attempts are preserved in full:

1. The downstream length proof unfolded the new recursor past the syntactic form of its induction hypothesis. Omega treated the named and expanded tail lengths independently. Replacing one simp argument with value_cons repairs the proof; this is not a mathematical counterexample.
2. The exhaustive strict audit rejects the remaining 41 partial roots, as required by the unchanged policy.

UUID directories retain authoritative raw diagnostics and exact submitted sources. Semantic-label logs are convenience copies. `reconcile.py` is an evidence writer, not a filesystem-read-only checker: it rewrites only current derived evidence and chunks, while verifying historical manifests without changing them. Its checks include source/object/import bindings, exact affected closure, narrow proof changes, full recursive closure, one-companion delta, singleton replay and historical preservation.

The complete recursive TSV is retained with 207 ordered row-aligned chunks and a reconstruction hash in `audit-export/manifest.json`. Concatenate chunk bytes in manifest order without added separators or headers. The evidence manifest seals every checkpoint file except itself.

Entry points: `python checkpoints/light-eft-records-value-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-records-value-pilot-20261016/run.py pilot`, `build`, `audit`, `replay`; and the noncompiling evidence writer `python checkpoints/light-eft-records-value-pilot-20261016/reconcile.py`. All compiler/checker entry points use the unchanged universal exclusive supervisor with persisted preflights and source-bound receipts.

Publication uses additive source/evidence commits with `[skip ci]`, after checking remote state. Terminal observations record no compiler/checker, a free common lock, and repository CI status. The worker stops for sequential independent review.
