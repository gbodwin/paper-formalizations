# StoredDrawLookup.typedValue total-recursor pilot

Tested source: `42fcd87704e918d0946d75d57e9cbf3bada56233`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

Fresh inspection confirmed the requested lookup recursion and exact **69-module affected closure**, with **417 inherited objects**. This separate repair removes only `LightEFTSpanners.StoredDrawLookup.typedValue._unsafe_rec`: **44 → 43** partial roots, with none added. The unchanged strict all-owner gate still fails. CI remains off. A clean final exact-source gate, Theorem 34, physical-runtime claims and whole-paper completion remain open. The worker pauses for independent review.

## Accepted baseline, capacity and preservation

The parent reports independent acceptance of source `5f15ce94d6728e534beb0bdb009d3929f78ed357`, evidence `e8358f2b7d1c34ec78d0b52964dc3bc1a39ff059`. That review inspected committed source/evidence, not live objects or fresh execution. This worker independently rehashed all 486 baseline source/object bindings before reuse. Initial checks found a clean worktree, no compiler/checker and the universal lock free.

The larger closure was budgeted before compilation: the 486 copied objects occupy 107,208,920 bytes; free disk after copying was 21,284,728,832 bytes. The memory limit is 17,179,869,184 bytes (16 GiB), with about 6.16 GB current cgroup usage at that observation. `capacity-budget.json` records these observations and concurrency one. The supervisor persists a fresh process/resource preflight for each invocation and requires more than 2 GiB free disk. No other compiler/checker or default Lake build is started; all previous outputs are preserved.

The parent reported a disconnect notification near 16:23 UTC. A fresh shell/process/receipt check at 16:24:54 UTC verified the environment was connected and the existing build was continuing: 65 modules had completed, exactly one Lean child held the universal lock, and the last completed child was reaped. That observation is preserved in `evidence/connection-check-162454.json`. No duplicate compiler or replacement build was started; the existing supervised session then completed all 69 modules. No execution resumption was inferred solely from the notification.

All historical checkpoint contents and qualifications remain unchanged, including failures, the Controller 494-preflight/495-receipt gap, historical aggregate-prefix OOM/internal parallelism, prior theorem-count correction and reconciliation-writer-label correction. The historical-tree inventory compares every existing checkpoint entry against the parent commit. No canceled workspace or other paper was accessed.

## Exact first-match and nested-payload semantics

The original domain is `key : ℕ` and `TypedBank n = List (ℕ × List (List (Fin n × Fin n)))`. The result is the complete payload of the first record with key equality, or [] if no key matches. The replacement uses explicit total List.rec with the same nil and cons equations, both proved by `rfl`.

The universal legacy theorem compares the actual accepted implementation with a byte-identical copy of the new body for every n, natural key and bank. It proves equality of the entire nested list and **depends on no axioms**. No bounded-key, distinct-key, sorted-bank, nonempty-payload, graph-validity or payload-validity hypothesis is added. Keys are unrelated to n and may exceed machine-word ranges. Duplicate keys retain first-match priority. An empty first matching payload wins over later nonempty matches. A payload `[[]]` remains distinct from `[]`.

Every selected draw list, empty draw, repeated/reversed endpoint pair, loop, order and multiplicity is preserved. No normalization, merging, deduplication or validation is introduced. Fin n remains the original endpoint type. At n=0 the outer bank and natural keys can be nonempty, while individual draws must be empty; fixtures exercise matching `[[],[]]`, empty-first-match and missing-key cases. Singleton-vertex loops are also tested. This is full output equivalence without an additional runtime claim about evaluating List.rec. Existing executable lookup transitions, values, step counts and trace contracts remain unchanged.

The target definition and its two explicit equations are the only changes in StoredDrawLookupEncoding. Its original `value_encoded` theorem statement and body remain byte-identical. **The entire StoredForestInput namespace, including typedInputs, is byte-identical.** The same is verified by exact suffix comparison, not merely by header counting.

Two supporting proof arguments in StoredForestDrawSize change from unfolding typedValue to the explicit typedValue_cons equation, in the cons cases of `lookup_count` and `lookup_cells`. Both theorem headers and all definitions in that file are unchanged. All other 484 closure source files are unchanged. The accepted namespace-aware source check retains the full second namespace even though it contains no theorem declaration. No audit roots are filtered by this source check.

## Boundary checks and strict rebuild

Fresh metadata confirms safe, total, computable status, explicit List.rec, absence of self-reference and absence of the target partial companion. Universal nil/cons examples compile. All 18 complete-payload fixtures pass: zero/large/missing natural keys, duplicate-key order, empty first match, `[[]]` versus `[]`, unrelated prefix/suffix entries, ordered nested data with duplicates/reversals/loops, and actual zero/singleton-vertex inputs.

The isolated `.lake/draw-typed-pilot/lib/lean` began with 486 verified object copies. Every module in the source-derived 69-module transitive closure was invalidated before rebuilding, forcing fresh compilation even when intermediate object bytes remained unchanged. All 69 modules, including the aggregate, received successful fresh strict compilation. The other 417 objects retain accepted source, direct-import and object hashes. The complete graph/closure is in `affected-closure.json`; `source-object-provenance.json` distinguishes new compilation from inherited objects.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine pinned dependencies remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. Audit/replay paths contain the isolated outputs, pinned packages and official toolchain without old project fallback. No dependency update, runtime shim, warning suppression or blanket noncomputable conversion occurs. This remains incremental validation; clean final exact-source validation is still required.

## Unchanged exhaustive audit and singleton replay

The full actual-owner audit and official resolver are unchanged except output-directory substitution. All owners and recursive types/bodies, opaque values, inductive families and recursor rules retain their existing coverage. No root, generated name or remaining partial is filtered or allowlisted.

Fresh audit: 9220 actual-owner project roots, 60639 recursive constants, 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms in the full closure. Exactly the target companion disappears; the other 43 partial roots remain unchanged, including typedInputs. The strict audit exits 1 with exactly 86 findings, one root and one recursive finding per remaining partial. This is **not** a passing strict gate. `owner-inventory-delta.json` records the complete delta: nine generated roots disappear and two explicit equations appear, with no actual-owner changes.

The official resolver selects exactly one module/object for LightEFTSpanners.StoredDrawLookupEncoding, and the supervisor repeats filesystem resolution under the universal lock. Official `leanchecker -v LightEFTSpanners.StoredDrawLookupEncoding` passes with exactly one replay line. No aggregate-prefix replay occurs. LEAN_SYSROOT identifies the official toolchain. A passing singleton replay does not discharge the all-owner no-partial gate; unchanged typedInputs remains explicitly covered by that audit.

## Receipts, raw diagnostics and review exports

All 75 unique source-bound receipts have persisted preflights, exact commands/options, source snapshots/hashes, lock inode, PIDs, UTC/monotonic timing and reaping results. There are 565 submitted-source entries. Reconciliation verifies one lock inode, strict non-overlap and every child reaped. Warning classification counts anchored diagnostic headers rather than hints or option text; zero warning headers occur.

Two nonzero Lean attempts are preserved:

1. Initial StoredForestDrawSize compilation unfolded the recursor past the form used by its induction hypotheses. The explicit cons equations repair those two proof steps. The arithmetic tactic's possible assignments concern unconnected elaborated expressions, not mathematical counterexamples or false paper statements. Raw diagnostics and submitted sources remain in the UUID directory.
2. The unchanged exhaustive audit rejects the remaining 43 partial roots.

No historical failure is discarded. UUID directories are authoritative; semantic-label logs are convenience copies. `reconcile.py` is explicitly an evidence writer: it does not execute Lean/checker, but rewrites current derived JSON and audit chunks. The historical label correction remains additive in RECONCILIATION_SCOPE.md.

Reconciliation checks all 486 source/object/import bindings, the exact affected closure, unchanged theorem statements/bodies and typedInputs, the two supporting proof arguments, source-bound receipts/preflights, all snapshots, exhaustive closure, exact one-companion removal, singleton resolution and prior manifests. The full dependency TSV is retained alongside 207 ordered row-aligned chunks with per-chunk and reconstruction hashes. Concatenate listed bytes without extra headers or separators.

Entry points: `python checkpoints/light-eft-draw-typed-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-draw-typed-pilot-20261016/run.py pilot`, `build`, `audit`, or `replay`. `python checkpoints/light-eft-draw-typed-pilot-20261016/reconcile.py` regenerates derived evidence before sealing. Every compiler/checker invocation uses the unchanged universal supervisor.

Publication is additive with `[skip ci]`. The worker stops with no compiler/checker running and the universal lock free, awaiting independent review. No CI, website change or broader paper claim is introduced.
