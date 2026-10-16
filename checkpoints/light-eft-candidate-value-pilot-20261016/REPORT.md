# StoredCandidateDrawLookup.value total-recursor pilot

Tested source: `8723e2833692780b0fc5de7096be0fb50d19dcbc`. Branch: `light-eft-spanners-checkpoints`. Exact source/object binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredCandidateDrawLookup.value._unsafe_rec` disappears: **41 → 40 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **80 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other repair target is started.

## Accepted baseline and resources

The parent independently accepted source `a047d25d17a9729aee544844d301353e5af4ada9` and evidence `ce79ae300099dc7ea833f0c9d5d159a4b95d287b` as a bounded repair. Review was finished before execution. This records committed source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

The initial tracked worktree was clean at the accepted evidence commit, with no active Lean/Lake/checker and the universal lock free. Approximately 20 GiB workspace disk was free; memory limit was 16 GiB, usage about 6.2 GiB. The worker rehashed all 486 accepted live source/object bindings and all 851 entries of the parent evidence manifest. The source-import closure was independently rederived as 17 affected modules and 469 unaffected modules. Initial capacity/process observations and individual invocation preflights are preserved.

All historical checkpoint trees remain unchanged. Earlier failed attempts, Controller's 494-preflight/495-receipt qualification, the aggregate-prefix OOM/sequencing violation, theorem-count correction and evidence-writer-label correction are retained. No deleted/canceled ChatGPT workspace is accessed or recreated. Work stays on Light EFT; no website or other paper is changed.

At 17:22 UTC the parent reported an environment-disconnected event. A live check at 17:23:25 UTC succeeded in the existing workspace: no active compiler/checker, lock free, all 486 live source/object bindings reverified and all 23 receipts showing reaped children. Build, audit and replay were already complete. No process was restarted or duplicated; no user action was required. `evidence/interruption-reconciliation.json` preserves the observation.

## Universal full-payload semantics

The original equation-compiler recursion for value is replaced by explicit total `List.rec`. The original `StoredEdges.same key i` comparison and complete matching payload are unchanged. The result is the first matching nested bank, or [] if none matches. Explicit nil/cons equations are proved by `rfl`.

`LegacyEquivalence.lean` imports the exact hash-bound accepted implementation and proves equality of complete nested output lists for every original key and bank. Its replacement body is byte-identical to production. Induction applies congrArg to the unchanged conditional. The universal equality theorem uses **no axioms**. Before-source, replacement body, all legacy object hashes and the new comparison-object hash are saved. The comparison intentionally uses preserved legacy objects; the new audit and replay use only isolated current project outputs.

No sortedness, bounded-endpoint, graph validity, distinct-key or nonempty-payload premise is introduced. Edge keys have arbitrary natural endpoints, including loops and large values. Undirected matching retains reversed-key behavior. Duplicate or reversed matching keys retain first-match priority. An empty first matching payload remains empty even if a later match is nonempty. Nested bank keys, duplicate keys, complete ordered draw lists, empty draws, loops and repeated/reversed edges remain unrestricted and are preserved exactly.

Nineteen executable fixtures compare complete nested bank outputs using structural equality, not lengths or projections. Cases cover empty and missing banks, matching keys in both orientations, duplicate/reversed first matches, empty first payloads, unrelated prefixes and suffixes, missing queries, loops, arbitrary natural endpoints including 10^20, and full nested payload order/content. Universal nil/cons checks and metadata checks verify safety, totality, computability, explicit List.rec, no self-reference and no partial companion. This is semantic preservation, not a physical-runtime claim about evaluation.

## Narrow source scope

Two production Lean files change. `StoredCandidateDrawLookup.lean` contains the implementation repair. It replaces value and adds two equation theorems. The prefix containing Bank, State and transition is byte-identical. The entire suffix beginning at `def steps` is byte-identical: steps, lookup_trace, steps_le and all existing theorem hypotheses and proof bodies remain unchanged. All other 484 closure source files are byte-identical.

In `StoredCandidateDrawEncoding.lean`, only the lookup value_encoded proof changes its simp arguments from value/typedValue to value_cons/typedValue_cons. Both accepted typed implementations and their equation proofs are byte-identical; all six pre-existing theorem statements in this file are unchanged. The original-candidate typed namespace is entirely unchanged. `typed-implementation-preservation.json` binds the exact one-line proof change. No blanket noncomputable conversion or changed hypothesis occurs.

## Complete affected rebuild

All 17 affected modules, including the aggregate, receive fresh strict compilation. The other 469 objects retain accepted source, direct-import and object hashes, classified separately from fresh execution. Before building, every affected state is removed so even equal intermediate object bytes cannot skip required recompilation. The evidence writer rederives imports from current source and verifies the complete affected closure again.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, remains unchanged. All nine dependency revisions are checked against lake-manifest.json before each runner invocation, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Toolchain executables, manifest and unchanged supervisor hashes are recorded and reconciled. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, warning suppression, dependency change, shim or alternate runtime occurs.

## Exhaustive recursive audit and singleton replay

The complete actual-owner audit and official resolver are unchanged apart from output-directory substitution. Coverage includes all project owners, recursive types/bodies, opaque values, inductive families and recursor rules; no generated name, partial root or remaining violation is filtered or exempted.

Fresh audit reports 9203 actual-owner roots, 60622 recursive constants and 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only propext, Classical.choice and Quot.sound occur in the full closure. Exactly the target partial companion disappears; all other 40 partial roots remain unchanged. The actual-owner inventory removes nine generated roots and adds six, including the two explicit value equations and generated steps match helpers; steps source itself is byte-identical. The unchanged typedValue.eq_1 generated declaration also changes actual owner within the rebuilt closure. `owner-inventory-delta.json` records these changes without filtering or exclusions. The strict audit exits 1 with 80 root/recursive findings. This is a failing strict gate, not final acceptance.

The official resolver selects exactly one module/object for `LightEFTSpanners.StoredCandidateDrawLookup`. The unchanged supervisor repeats singleton resolution under the universal lock. `leanchecker -v LightEFTSpanners.StoredCandidateDrawLookup` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay LEAN_PATH contains isolated new project outputs, pinned packages and official toolchain, without historical project fallback. Passing singleton replay does not discharge remaining partials. This is incremental validation; clean final validation remains required.

## Receipts, failures and review exports

23 unique source-bound receipts and persisted preflights include 513 submitted-source entries. They record exact commands/options, source snapshots/hashes, lock inode, child PIDs, UTC/monotonic times, exit status and reaping. Reconciliation verifies one lock inode, non-overlap, all snapshots and all children reaped. At most one compiler/checker is active. Zero anchored warning headers occur; hints and option names are not counted as warnings.

Two nonzero invocations are preserved. The first encoding compile exposed a simp mismatch between expanded recursors and the named induction hypothesis, plus a strict unused-simp-argument diagnostic. The repair uses both explicit cons equations in the same simp list; it changes neither implementation nor theorem hypotheses and is not a mathematical counterexample. The second is the unchanged exhaustive audit rejecting the remaining 40 partial roots. Both UUID directories preserve raw diagnostics and exact submitted sources. All semantic fixtures pass, and all historical failed attempts remain unchanged. UUID directories are authoritative; semantic-label logs are convenience copies.

`reconcile.py` is explicitly an evidence writer, not a filesystem-read-only checker. It regenerates only current derived evidence and chunks; historical manifests are verified without changes. Checks cover source/object/import bindings, the rederived affected closure, unchanged steps/proofs and typed source, the complete recursive closure, exact one-companion delta, singleton replay, receipts and prior evidence preservation.

The full recursive dependency TSV is retained with 207 ordered row-aligned chunks and reconstruction hash in `audit-export/manifest.json`. Concatenate chunk bytes in manifest order without extra headers or separators. The evidence manifest seals all checkpoint files except itself.

Entry points: `python checkpoints/light-eft-candidate-value-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-candidate-value-pilot-20261016/run.py pilot`, `build`, `audit`, `replay`; and the noncompiling evidence writer `python checkpoints/light-eft-candidate-value-pilot-20261016/reconcile.py`. Every compiler/checker invocation uses the unchanged universal exclusive supervisor with persisted preflights and source-bound receipts.

Publication uses additive source/evidence commits with `[skip ci]`, after checking remote state. Terminal observations record no compiler/checker, a free common lock, current resources and repository CI statuses. The worker stops for sequential independent review.
