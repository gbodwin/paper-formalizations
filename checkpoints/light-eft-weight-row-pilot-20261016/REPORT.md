# StoredOriginalWeightMatrix.row total-recursor pilot

Tested source: `b87e2d11d0c437b868723f40ccf988de8c5ac42a`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredOriginalWeightMatrix.row._unsafe_rec` disappears: **36 → 35 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **70 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other target is started.

## Accepted baseline, resources and preservation

The parent independently accepted source `5477df1f6fadd5d1bb10ecda9862e2ec59b155ea` and evidence `023b257c6d6ccb7b2d09a36c15b6ec2fead680c1` as a bounded incremental repair. Review was finished before execution. This records committed source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

Initial tracked state was clean at the accepted evidence commit. No Lean/Lake/checker was active and the universal lock was free. Approximately 19 GiB disk was free; the cgroup memory limit was 16 GiB with about 7.2 GiB used. All 486 accepted live source/object bindings and all 969 parent-manifest entries were rehashed. The independently rederived source-import closure has 39 affected modules and 447 unaffected modules.

Every compiler/checker invocation requires at least 4 GiB cgroup headroom and 4 GiB system MemAvailable before admission. Individual memory-admissions.jsonl observations are reconciled with receipts, and memory-admission-summary.json records their minima. This observes available memory without claiming a reservation or treating the supervisor disk gate as a memory gate. Both MemoryAdmission.py and the exclusive supervisor are unchanged from the accepted checkpoint. Individual supervisor preflights retain process/disk/memory observations. Across all 45 invocations, minimum cgroup headroom was 9188450304 bytes (about 8.56 GiB), and minimum system MemAvailable was 17433858048 bytes.

All historical checkpoint trees and failed attempts remain unchanged, including prior execution gaps, aggregate-prefix OOM/sequencing qualification, theorem-count correction, evidence-writer-label correction and interruption records. No deleted/canceled ChatGPT workspace is accessed or recreated. No website or other paper is changed.

## Universal complete-output semantics

The row recursion is replaced by explicit total `Nat.rec` on length k. Its accumulated result is a function from starting column to `List ℚ`: the zero case returns []; the successor case prepends the unchanged `StoredOriginalWeightLookup.value (i,col) bank` and evaluates the tail at col+1. Explicit zero/successor equations are proved by `rfl`.

`LegacyEquivalence.lean` imports the exact hash-bound accepted implementation and proves equality of the complete output list for every original bank and arbitrary natural row index i, starting column j and length k. Induction generalizes j and invokes its hypothesis at j+1, preserving the per-cell increment and output order. The replacement body is byte-identical to production. The equality theorem reports only **propext and Quot.sound**; no axiom or mathematical hypothesis is added. Before-source, replacement body, legacy object hashes and comparison-object hash are retained. The comparison uses accepted legacy objects; the new audit/replay use isolated current project outputs.

There is no dimension bound on i, j or k, no requirement of starting at zero, and no validity/sortedness/distinctness/nonnegativity assumption on the bank. Length zero returns [] for every bank and both indices, including very large indices. Positive lengths emit every rational cell in increasing column order with the row index fixed. The existing lookup's first-match priority, reversed-key behavior, signed and fractional payloads, zero first matches and absent-cell zero remain unchanged. No row reversal, truncation or filtering is introduced. This is full semantic equality, not a new physical-runtime claim about recursor evaluation.

Twenty fixtures compare complete rational lists, not lengths or projections. They cover zero lengths, empty banks, nonzero starting columns, nonzero and very large row indices, a starting column of 10^20 and its successor, exact signed/fractional sequences, missing cells, diagonal loops, reversed bank keys, duplicate-key priority, zero before later nonzero matches, large rational numerators and a 32-cell row. Universal zero/successor examples and metadata checks establish safety, totality, computability, explicit Nat.rec, no self-reference and no partial companion.

## Source scope

Two production Lean files change. StoredOriginalWeightMatrix.lean replaces row and adds zero/successor equations; its prefix and the rows definition remain byte-identical. Both existing theorem statements are unchanged. In row_length, one simp argument is changed from row to row_succ before compilation, based on the accepted analogous recursor repairs. rows_length remains byte-identical.

StoredOriginalWeightMatrixEncoding.lean changes one rewrite argument in row_ofFn, from row to row_succ. Its three existing theorem statements are unchanged, and rows_ofFn and execute_encoded proof bodies remain byte-identical. All other 484 closure source files are unchanged, including the accepted lookup value, steps and typed weight definitions.

## Complete affected rebuild and exhaustive audit

All 39 affected modules, including the aggregate, receive fresh strict compilation. The other 447 objects retain verified accepted source, direct-import and object hashes. Every affected state was removed before building so equal intermediate object bytes cannot skip required compilation. The evidence writer independently rederives imports and the closure from current source. Inherited historical receipts are not counted as fresh execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, remains unchanged. All nine dependency revisions are checked before each runner invocation, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Exact toolchain, manifest and supervisor hashes are recorded and reconciled. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, dependency change, warning suppression, blanket noncomputable conversion, alternate runtime or shim occurs.

The actual-owner audit and official resolver are unchanged apart from output-directory substitution. All project owners, recursive types/bodies, opaque values, inductive families and recursor rules remain covered. No generated name, partial root or remaining violation is filtered, exempted or allowlisted.

Fresh audit: 9176 actual-owner roots, 60595 recursive constants and 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. Exactly the row companion disappears; all other 35 partial roots remain unchanged, including the separate rows companion. The strict audit exits 1 with 70 root/recursive findings. All generated-name and owner changes are recorded in owner-inventory-delta.json. Nine generated roots disappear and six appear, including row_zero/row_succ and generated rows match helpers; rows source itself is byte-identical. The generated row.eq_1 declaration also changes actual owner within the rebuilt closure. These declarations remain covered, without filtering or exemptions. This is a failing strict gate, not final acceptance.

## Singleton replay and raw evidence

The official resolver selects exactly one object/module for `LightEFTSpanners.StoredOriginalWeightMatrix`; the supervisor repeats singleton resolution under the universal lock. `leanchecker -v LightEFTSpanners.StoredOriginalWeightMatrix` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay LEAN_PATH contains isolated current project outputs, pinned packages and official toolchain without historical project fallback. Singleton replay does not discharge remaining partials; clean final exact-source validation is still required.

45 unique source-bound receipts have persisted supervisor preflights and individual memory-admission observations. They contain 535 submitted-source entries, exact argv/options, snapshots/hashes, lock inode, child PIDs, UTC/monotonic times, exits and reaping. Reconciliation verifies every snapshot, one lock inode, non-overlap and all children reaped. Concurrency is one. Zero anchored warning headers occur; hints and option names are not counted as warnings.

Two nonzero invocations are preserved. The first downstream row_ofFn compile could not match its named induction hypothesis after unfolding the new recursor. The single row_succ rewrite substitution repairs that proof with no statement change; this is not a mathematical counterexample. The other nonzero invocation is the unchanged exhaustive audit rejecting the remaining 35 partial roots. All full-row fixtures pass.

UUID directories preserve authoritative raw diagnostics and exact submitted sources; semantic-label logs are convenience copies. All historical failed attempts remain unchanged. `reconcile.py` is explicitly an evidence writer: it regenerates current derived evidence/chunks without invoking Lean/checker and verifies historical manifests without changing them. Its checks cover source/object/import bindings, exact closure, rows preservation, existing hypotheses, complete recursive audit, one-companion delta, singleton replay, memory admissions, receipts and historical preservation.

The complete recursive TSV is retained with 207 ordered row-aligned chunks and reconstruction hash in `audit-export/manifest.json`. Concatenate bytes in manifest order without extra headers or separators. The evidence manifest seals all checkpoint files except itself.

Entry points: `python checkpoints/light-eft-weight-row-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-weight-row-pilot-20261016/run.py pilot`, `build`, `audit`, `replay`; and noncompiling writer `python checkpoints/light-eft-weight-row-pilot-20261016/reconcile.py`. Every compiler/checker call uses the unchanged exclusive supervisor and memory admission helper.

Publication uses additive source/evidence commits with `[skip ci]` after remote-state checks. Terminal observations record no compiler/checker, a free common lock, resources and repository CI statuses. The worker stops for sequential independent review.
