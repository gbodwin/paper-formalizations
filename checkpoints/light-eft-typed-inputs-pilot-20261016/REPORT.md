# StoredForestInput.typedInputs total-recursor pilot

Tested source: `3659611df7b31736793bbd547aa5b494f73b7cc5`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

Fresh inspection confirms the complete **69-module affected closure** with **417 inherited objects**. This separate bounded repair removes exactly `LightEFTSpanners.StoredForestInput.typedInputs._unsafe_rec`: **43 → 42** partial roots, with none added. The unchanged exhaustive strict gate still fails. CI remains off. A clean final exact-source gate, Theorem 34, physical-runtime claims and whole-paper completion remain open. The worker stops for independent review before any further target.

## Accepted baseline and capacity

The parent reports independent acceptance of source `42fcd87704e918d0946d75d57e9cbf3bada56233`, evidence `5f096422d38e0c101142adbd0850f78042519d1a`, as a scoped incremental repair. This records review of committed source/evidence, not fresh reviewer execution or live-object inspection. The worker independently rehashed all 486 baseline live source/object bindings before reuse. Initial checks found a clean worktree, no compiler/checker and the universal lock free.

The larger closure was budgeted before execution. `capacity-budget.json` records the total bytes of the 486 copied objects, about 20 GiB free disk after copying, the 16 GiB memory limit and current usage. Compiler/checker concurrency is one; every invocation gets a persisted process/resource preflight and requires more than 2 GiB free disk. All prior artifacts remain preserved. No default Lake build or unrelated-paper build was run.

Historical checkpoint contents and qualifications remain unchanged: failed attempts, Controller's 494-preflight/495-receipt gap, the aggregate-prefix OOM/internal-parallelism incident, earlier theorem-count correction and evidence-writer-label correction. The historical-tree inventory compares all existing checkpoint entries against the parent commit. No deleted/canceled ChatGPT workspace was accessed or recreated.

## Universal complete-record-list equivalence

The input is arbitrary n, typed bank, starting natural index i and list of typed edge lists. The replacement is an explicit total List.rec whose accumulated result is a function `ℕ → List (StoredComponentRecord.TypedInput n)`. At each draw it emits the **unchanged** map over that draw's canonical roots, then appends the tail evaluated at i+1. At nil it returns []. Both equations are proved by `rfl`.

`LegacyEquivalence.lean` imports the actual hash-bound accepted implementation and proves equality of the complete output record list for every original input. The proof generalizes the starting index and applies its induction hypothesis at i+1. The unchanged root map is prepended by List.append. Thus the theorem covers all record fields, root order, concatenation order, attached payloads and the increment per input draw—not per root or emitted record. The comparison body is byte-identical to production. Its axioms are exactly `propext`, `Classical.choice` and `Quot.sound`.

No forest/acyclicity, distinct-edge, loop-free, sorted-input, valid-payload, distinct-bank-key or bounded-index premise is added. Starting indices and bank keys are arbitrary naturals. Canonical roots, component vertices, host-edge filtering and lookup are the existing functions. Their ordering and behavior are preserved. Input edge lists can contain cycles, loops, duplicate or reversed edges. Host filtering still omits loops as before, while attached draw payloads retain their complete contents, including loops, duplicate/reversed entries and empty draws. Duplicate bank keys and empty first matching payloads retain the accepted lookup behavior. Endpoint bounds remain the original Fin n type.

The zero-vertex case admits actual inputs such as a nonempty list of empty edge lists and arbitrary starting index/bank, producing no component records. The singleton case admits isolated vertices and loop-only inputs. Empty edge lists at positive n still emit one record per isolated component. The starting index advances by one for each draw regardless of the number of roots emitted. Large indices are not truncated. This is output equivalence, not an additional physical-runtime claim about the new recursor's evaluation.

## Source scope and boundary checks

**The entire accepted StoredDrawLookup namespace is byte-identical**, including its implementation, nil/cons equations and value_encoded theorem. All three existing theorem statements and bodies in StoredDrawLookupEncoding are unchanged. Only typedInputs and its two explicit equations are added/replaced.

Two downstream proofs change one simp argument each: `typed_inputs_length` in StoredForestHostSize and `typedInputs_ofFn` in StoredForestInputIndices use typedInputs_cons instead of unfolding typedInputs. All four existing theorem headers across those files and every definition remain unchanged. The other 483 closure source files are byte-identical. No hypothesis or mathematical coverage claim changes.

Fresh metadata checks establish safe, total and computable status, explicit List.rec, no self-reference and no partial companion. Universal nil/cons examples compile. Seventeen executable fixtures compare **complete records**, using test-only structural equality for both the outer component record and nested host record. Expected outputs specify literal IDs, ordered vertex lists, host edge lists and full attached draw lists; they are not checks of lengths or projections alone.

Fixtures cover zero/singleton vertices; empty and loop-only graphs; isolated components; cycles; repeated/reversed edges; missing, empty and duplicate-key payloads; arbitrary large starting indices; repeated draws; component-root order; host filtering; and concatenation order. In particular, a draw with three roots followed by a connected draw checks that the latter uses the next draw index, not an index advanced by three. Different ordered draw lists check the associated ID/payload attachment ordering.

## Complete affected rebuild and provenance

The isolated `.lake/typed-inputs-pilot/lib/lean` began with 486 verified accepted object copies. The source-derived import graph identifies all 69 affected modules rooted at StoredDrawLookupEncoding. Every affected state was removed before building, forcing fresh compilation even if intermediate object bytes remained equal. All 69 modules, including the aggregate, received successful fresh strict compilation. The other 417 objects retain accepted source, direct-import and object hashes, individually classified in source-object-provenance.json. Historical receipts are not counted as new execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine dependencies remain pinned, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. The audit/replay search path contains the isolated outputs, pinned packages and official toolchain without old project fallback. No dependency update, runtime shim, alternate runtime, blanket noncomputable conversion or warning suppression occurs. This remains incremental validation; clean final validation is still required.

## Unchanged exhaustive audit and singleton replay

The actual-owner audit and official resolver are copied unchanged except output-directory substitution. All project owners, recursive types/bodies, opaque values, inductive families and recursor rules retain the same coverage. No root, generated name or remaining partial is filtered, allowlisted or excluded from the strict policy.

Fresh audit: 9213 actual-owner roots, 60632 recursive constants, 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms in the full closure. Exactly the target companion disappears; all other 42 partial roots remain unchanged. Strict audit exits 1 with 84 findings: one root and one recursive finding per remaining partial. This is **not** a passing strict gate. owner-inventory-delta.json records the full generated-name and actual-owner changes.

The official resolver selects exactly one module/object for LightEFTSpanners.StoredDrawLookupEncoding; the supervisor repeats filesystem resolution under the universal lock. Official `leanchecker -v LightEFTSpanners.StoredDrawLookupEncoding` passes with exactly one replay line. LEAN_SYSROOT points to the official toolchain. No aggregate-prefix or multi-target replay occurs. Successful singleton replay does not discharge the full no-partial requirement.

## Receipts, failures and review exports

All 76 unique source-bound receipts have persisted preflights, exact commands/options, source snapshots/hashes, lock inode, child PIDs, UTC/monotonic times and reaping results. There are 566 submitted-source entries. Reconciliation verifies one lock inode, non-overlap and all children reaped. Warning classification counts anchored diagnostic headers, not hints or option names. Zero warning headers occur.

Three nonzero Lean attempts are preserved with raw diagnostics and submitted source:

1. The host-size length proof unfolded the recursor past the form of its induction hypothesis; the explicit cons equation repairs the single simp argument.
2. The indexed-list expansion similarly could not rewrite the unfolded tail with its induction hypothesis; its single cons-equation substitution repairs the proof.
3. The unchanged strict audit rejects the remaining 42 partial roots.

These are proof-interface repairs, not mathematical counterexamples. All historical failures remain untouched. UUID attempt directories are authoritative; semantic-label logs are convenience copies.

`reconcile.py` is accurately labeled as an evidence writer. It does not invoke Lean/checker but rewrites current derived JSON files, audit chunks and their manifest. The additive historical-label correction remains in RECONCILIATION_SCOPE.md. The writer verifies source/object/import bindings, full affected closure, unchanged lookup namespace and theorem headers, the two exact supporting proof changes, all receipts/preflights and snapshots, exhaustive recursive closure, the exact one-companion removal, singleton resolution and preserved prior manifests.

The complete dependency TSV is retained alongside 207 ordered row-aligned chunks, with per-chunk and reconstruction hashes. Concatenate bytes in manifest order without separators or extra headers. Entry points are `python checkpoints/light-eft-typed-inputs-pilot-20261016/legacy_compare.py` and `python checkpoints/light-eft-typed-inputs-pilot-20261016/run.py pilot`, `build`, `audit`, or `replay`. `python checkpoints/light-eft-typed-inputs-pilot-20261016/reconcile.py` regenerates derived evidence before sealing. Every compiler/checker invocation uses the unchanged exclusive supervisor.

Publication uses additive source/evidence commits with `[skip ci]`. The worker stops with no compiler/checker running and the lock free for independent review before another target. No CI, website change or final paper-validation claim is introduced.
