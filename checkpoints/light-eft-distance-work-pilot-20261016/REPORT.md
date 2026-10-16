# RationalDistance scanWork/tableWork bounded pilot

Tested source: `ea5017d9cbe674374bac972136f995a7248a9111`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

Exactly the two requested partial companions are removed, with none added: **52 → 50**. The unchanged complete-owner strict gate still fails. No CI is started. The worker pauses for independent review before another definition is repaired. Theorem 34, physical runtime claims and whole-paper completion remain open.

## Accepted prior review and reporting correction

The parent accepts source `9836cc5c9f529fa217a56dea19aea8be8f397ded` and evidence `d19a75220dee4b5226881f893a7999228efc59bd`. This records independent source/log/hash reconciliation, not fresh reviewer execution.

The prior `statement-preservation.json` and report said nine pre-existing theorems. That count was wrong: the old unanchored regex parsed **or** from the opening comment's phrase containing “theorem or”. There were **eight actual pre-existing theorem statements**, all unchanged. The original evidence and report remain byte-identical; the correction is additive in `evidence/prior-statement-count-correction.json`, including the original artifact hash, actual names and their accepted actual-owner inventory records.

`declarations.py` replaces that parser with a comment/string-aware scanner for ordinary line-start named Lean declarations. It masks nested block comments, line comments and quoted strings, handles inline attributes and primed names, and finds the body boundary while respecting binder-local `:=` and equation-style definitions. Regression checks explicitly reject the false comment match. It is a source reconciliation aid, not a substitute for Lean's parser or kernel. Read-only reconciliation reruns the tests and the prior/current statement comparisons. The new RationalDistanceWork module has **nine actual pre-existing theorem statements**, all byte-identical, plus four new equation lemmas.

Both prior and current validation remain incremental, using pinned dependency caches and recorded byte-identical import/object hashes. A **clean final exact-source gate remains required**. The historical Controller 494-preflight/495-receipt qualification and aggregate-prefix OOM/internal-parallelism violation remain preserved. All prior 772, 3,242, 2,725 and 5,161 manifest entries were rehashed unchanged.

## Exact repair and full-output equivalence

Only `RationalDistanceWork.lean` changes among the 486 closure sources. `scanWork` uses explicit `List.rec`; `tableWork` uses explicit `Nat.rec`. Their original argument/result types are preserved. Four explicit equations, scan nil/cons and table zero/successor, are proved by `rfl`. Existing value, cost and specification theorem statements are unchanged; their proofs refer to the explicit equations. The production `stepWork` definition is unchanged.

`RationalDistance.table` and its source file remain unchanged. The metadata check and complete audit explicitly confirm that its partial companion remains, outside this pilot and reserved for separate review.

The fresh legacy comparison imports the hash-bound prior implementations and copies the two replacement bodies byte-identically into a comparison namespace. It proves equality of the entire `Option ℚ × ℕ` scan output, then equality of the unchanged row-step's entire vector/counter output, and finally equality of the entire `Vector (Option ℚ) n × ℕ` table output for every round count. The old source snapshot and all 486 old object hashes are verified before compilation. The helper step body is also byte-identical to production. This preserves counters and every vector cell, not just a value projection. All three equality proofs strictly compile and use only `propext`, `Classical.choice` and `Quot.sound`.

The repaired definitions remain safe, nonpartial and computable, with the required explicit recursor and no self-reference or own partial companion. Boundary fixtures check nine complete Option/counter pairs: empty scans with finite and absent values, unreachable candidates, reachable candidates, absence preservation, finite improvement, repeated candidates, negative rational weights and zero weights. Seven complete vector/counter fixtures check zero rounds, unreachable vertices, one and multiple rounds, zero-weight edges and singleton graphs. One additional fixture checks the unchanged step function on an empty vector. A table call requires a target in `Fin n`, so no impossible `Fin 0` target is fabricated. All 17 fixtures pass.

No extra mathematical hypothesis, generated-name filtering, unsafe shim, blanket noncomputable change, warning suppression or axiom is introduced. The original unit-cost accounting remains the stated model; no bit-cost or physical-runtime claim is added.

## Validation provenance and complete audit

The isolated `.lake/distance-work-pilot/lib/lean` began with 486 verified copies from the accepted work-pilot object ledger. Three modules were newly strictly compiled: RationalDistanceWork, its unchanged dependent ExecutableVotingWork, and the aggregate. The other **483 objects are inherited**, with byte-identical source and direct-import/object bindings. `source-object-provenance.json` distinguishes every new compilation from every inherited object. Inherited objects are not counted as new executions. The audit is a fresh execution against this isolated complete object set, with all 486 current source snapshots bound to its receipt and no old project-path fallback.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Strict compilation uses `-j1 -DautoImplicit=false -DwarningAsError=true`. All three project compiles pass with zero warning headers.

The full owner audit and official target resolver are unchanged except output paths. The audit inventories **9,269 roots, 60,688 recursively visited constants and 48 opaque bodies**. It traverses every actual-owner root and recursive type/body, opaque value, inductive family and recursor rule. There are zero unsafe project roots, zero aggregate-owned declarations, and only the standard three axioms.

Exactly `LightEFTSpanners.RationalDistance.scanWork._unsafe_rec` and `LightEFTSpanners.RationalDistance.tableWork._unsafe_rec` disappear. All other **50 partial roots** remain unchanged; none is added. The strict audit exits 1 with **100 findings**, one root and one recursive finding for each remaining partial. The gate has not passed. The full owner-name delta removes 22 generated roots and adds six: four equation lemmas and two replacement generated proof helpers. All changes are owned by RationalDistanceWork. No name is excluded from the audit.

The official target resolver selects exactly one module/object for RationalDistanceWork, and the supervisor repeats filesystem resolution under the common lock. The single `leanchecker -v LightEFTSpanners.RationalDistanceWork` invocation passes with exactly one replay line. `LEAN_SYSROOT` points to the official toolchain. No aggregate-prefix replay or parallel worker is used.

## Evidence and handoff

Eight new source-bound UUID receipts cover legacy equivalence, three strict project compiles, executable/metadata checks, the complete audit, official target resolution and singleton replay. Every receipt has a persisted process/resource preflight with matching UUID and hash, source snapshots, full command/options, PID, lock inode, timestamps and reaping. Reconciliation verifies non-overlap and child reaping. The expected strict-audit rejection is the only nonzero invocation; raw diagnostics are retained. There were no development compilation failures. Diagnostic counts use anchored headers, not hints or option names.

The full dependency TSV is preserved and exported into **207** ordered row-aligned chunks with per-chunk and reconstruction hashes. `reconcile.py` checks the complete closure, exact two-companion difference, statement correction, source/object/import provenance, singleton resolution, receipts/preflights and prior evidence preservation. Concatenate chunks in manifest order without separators or repeated headers.

Entry points are `legacy_compare.py`, then sequential `run.py pilot`, `run.py build`, `run.py audit` (expected exit 1) and `run.py replay`; `reconcile.py` is read-only and invokes no Lean. Publication is additive with `[skip ci]`. No default Lake build, dependency update, website change, other-project proof work or automatic CI is used. The terminal state is idle for independent review.
