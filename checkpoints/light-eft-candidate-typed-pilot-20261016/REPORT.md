# StoredCandidateDrawLookup.typedValue total-recursor pilot

Tested source: `4f910953931b2398a74b96c518418f0aaf0be16b`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

Fresh inspection confirmed the requested small list-recursion target in StoredCandidateDrawEncoding and its exact 14-module transitive affected closure. The bounded repair removes only `LightEFTSpanners.StoredCandidateDrawLookup.typedValue._unsafe_rec`: **46 → 45** partial roots, with none added. The unchanged strict all-owner gate still fails. CI remains off. A clean final exact-source gate, Theorem 34, physical-runtime claims and whole-paper completion remain open. This checkpoint pauses for independent review.

## Accepted baseline and current bindings

The parent reports independent acceptance of source `b1781be65eae837ae917d21c01e9cca319dae0bb`, evidence `cdc965af780f6c41257de2db2de533cb1d628933`, including the complete exhaustive audit and preserved failures. That was committed-source/evidence review, not live-object inspection or fresh Lean execution. Here the worker independently rehashed all 486 baseline source/object bindings before reuse. Initial checks found a clean worktree, no live compiler/checker, the universal lock free, about 21 GiB free disk and a 16 GiB memory limit.

All accepted checkpoint contents and qualifications remain unchanged, including prior failed attempts, the Controller 494-preflight/495-receipt gap, the historical aggregate-prefix OOM/internal-parallelism violation, the earlier theorem-count correction and the reconciliation-writer-label correction. The new historical-tree inventory compares every existing checkpoint entry against the parent commit. No canceled workspace or other paper was accessed.

## Full first-match and nested-payload semantics

The original function takes `e : Sym2 (Fin n)` and a list of typed endpoint-pair/payload records. It returns the first payload whose undirected endpoint pair equals e, or [] if no record matches. The replacement uses explicit total `List.rec`, returning [] at nil and choosing the current payload on a matching cons. Both explicit nil/cons equations are proved by `rfl`.

`LegacyEquivalence.lean` imports the actual hash-bound accepted implementation and proves equality of the complete nested payload for every n, e and bank. The replacement body is byte-identical to production. The proof uses only `propext` and `Quot.sound`. No unique-key, orientation, loop-free, ordering, nonempty-payload, graph-validity or payload-validity premise is added.

First-match priority includes duplicate and reversed keys. A matching **empty payload wins**; a later nonempty matching record is ignored in the returned result. The selected payload is returned unchanged: repeated natural indices, unrestricted index magnitudes, empty draw lists, empty individual draws, repeated edges, loops, reversed edges and their original ordering/multiplicity are all retained. It is not merged with later records, normalized, sorted or deduplicated.

Endpoints remain `Fin n`, exactly as in the original type. For n=0, there is no `Sym2 (Fin 0)` query. A separate Lean example proves this impossible-input case by eliminating a Fin-0 endpoint; no nonexistent query is fabricated. The singleton-vertex case is tested with a loop key and repeated loop data. These domain boundaries do not restrict the universal legacy theorem beyond its original types.

The executable lookup transition, value and step-count definitions are unchanged; their existing trace/encoding proofs compile. This is full output equivalence without an additional runtime claim about evaluating the new recursor.

Only the target definition and its two explicit equations change. Both existing `value_encoded` theorem statements **and bodies** in StoredCandidateDrawEncoding remain byte-identical, as do all other declarations in that file—including the distinct `StoredOriginalCandidateRecords.typedValue` recursion. All 485 other closure source files are unchanged. The accepted comment-aware declaration scanner is applied separately to both explicit namespace blocks, retaining both fully qualified `value_encoded` names rather than conflating their repeated unqualified names. This source check does not change audit roots or coverage.

Fresh metadata checks confirm safe, total and computable status, explicit List.rec, no self-reference and absence of the target partial companion. Sixteen full-payload fixtures pass: empty/missing lookup, matching forward/reversed keys, reversed queries, first duplicate priority, empty first payload, unrelated prefixes/suffixes, loop keys, singleton vertices and nested payloads with duplicate indices, large indices, empty draws and repeated/reversed/loop edges. Universal nil/cons examples and the impossible n=0 query example also compile.

## Complete affected rebuild and inherited provenance

The isolated `.lake/candidate-typed-pilot/lib/lean` starts from 486 verified accepted object copies. The complete source-derived affected closure is:

- LightEFTSpanners.StoredCandidateDrawEncoding
- LightEFTSpanners.StoredSortedCandidateInput
- LightEFTSpanners.StoredSortedCandidateExecutable
- LightEFTSpanners.StoredOriginalCandidateSupport
- LightEFTSpanners.StoredOriginalCallerBudget
- LightEFTSpanners.StoredOriginalGraphCaller
- LightEFTSpanners.StoredOriginalGraphExecution
- LightEFTSpanners.StoredOriginalGraphExecutable
- LightEFTSpanners.StoredCandidateBankRepresentation
- LightEFTSpanners.StoredOriginalOrderRepresentation
- LightEFTSpanners.StoredOriginalGraphOutput
- LightEFTSpanners.ComputableOriginalGraphGuarantee
- LightEFTSpanners.StoredOriginalGraphGuarantee
- LightEFTSpanners (aggregate compilation only)

All 14 affected states were invalidated before rebuilding, forcing fresh compilation even when intermediate object bytes stayed identical. All 14 strictly compile. The other 472 objects retain verified accepted source, direct-import and object hashes. `source-object-provenance.json` identifies fresh and inherited objects individually; no old receipt is counted as a new execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine dependency revisions remain pinned, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. Audit/replay search paths contain the isolated project objects, pinned packages and official toolchain, without old project fallback. No default Lake build, dependency update, runtime shim, warning suppression or blanket noncomputable conversion occurs. Validation remains incremental; a clean final exact-source gate is still required.

## Unchanged exhaustive audit and guarded replay

The complete actual-owner audit and official target resolver are copied unchanged except output-directory substitution. All owners and recursive types/bodies, including opaque values, inductive families and recursor rules, retain their existing coverage. No root, generated name or remaining partial is filtered or allowlisted.

Fresh audit: 9234 actual-owner project roots, 60653 recursive constants, 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms in the full closure. Exactly the target companion disappears; the other 45 partial roots remain unchanged. Strict audit exits 1 with exactly 90 findings, one root and one recursive finding per remaining partial. This is **not** a passing strict gate. The complete generated-name and actual-owner delta is in `owner-inventory-delta.json`: nine generated roots disappear and the two explicit equations appear; there are no actual-owner changes.

The official resolver selects exactly one module/object for `LightEFTSpanners.StoredCandidateDrawEncoding`; the supervisor repeats filesystem resolution under the universal lock. Official `leanchecker -v LightEFTSpanners.StoredCandidateDrawEncoding` passes with exactly one replay line. No aggregate-prefix replay is invoked. `LEAN_SYSROOT` points to the official toolchain. Replay does not itself discharge the exhaustive no-partial requirement, and the unchanged second recursion in this module remains explicitly audited as partial.

## Receipts, diagnostics and review exports

All 19 unique source-bound UUID receipts have persisted preflights, exact commands/options, source snapshots/hashes, lock inode, child PIDs, UTC/monotonic timing and reaping results. There are 509 submitted-source entries. Reconciliation verifies one lock inode, strict non-overlap and all children reaped. There are zero warning headers and no failed production, fixture, comparison or replay attempts. The sole nonzero Lean attempt is the expected strict audit rejection; its full raw diagnostics and submitted source are preserved. Historical failures remain unchanged.

Warning classification counts anchored diagnostic headers, not hints or option text. UUID attempt directories are authoritative; semantic-label logs are convenience copies. `reconcile.py` explicitly documents that it rewrites derived JSON and chunk outputs and does not run Lean/checker. It is not filesystem-read-only. `RECONCILIATION_SCOPE.md` preserves the additive correction to the historical label.

The evidence writer checks all 486 source/object/import bindings, the complete affected closure, exact source changes, both namespace-qualified theorem headers, receipts/preflights, source snapshots, exhaustive recursive closure, exact one-companion reduction, singleton resolution and preserved historical manifests. The complete dependency TSV is preserved and exported into 207 ordered row-aligned chunks with per-chunk and reconstruction hashes. Concatenate listed bytes without added separators or headers.

Entry points: `python checkpoints/light-eft-candidate-typed-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-candidate-typed-pilot-20261016/run.py pilot`, `build`, `audit`, or `replay`. `python checkpoints/light-eft-candidate-typed-pilot-20261016/reconcile.py` regenerates derived evidence before sealing. Every compiler/checker invocation uses the unchanged exclusive supervisor.

Publication uses additive source/evidence commits with `[skip ci]`. The worker stops with no compiler/checker running and the universal lock free, awaiting independent review. No CI, website changes or broader paper claim is introduced.
