# StoredOriginalWeightMatrix.rows total-recursor pilot

Tested source: `bfe8ac83406e6811c6038f04e91ad08000fcacdb`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json` and `evidence/source-object-provenance.json`.

This bounded incremental repair awaits independent review. Exactly `LightEFTSpanners.StoredOriginalWeightMatrix.rows._unsafe_rec` disappears: **35 → 34 partial roots**, with none added. The unchanged exhaustive strict gate still fails with **68 findings**. CI is absent, not passing. Clean final exact-source validation, Theorem 34, physical-runtime claims and whole-paper completion remain open. No other target is started.

## Accepted baseline, resources and preservation

The parent independently accepted source `b87e2d11d0c437b868723f40ccf988de8c5ac42a` and evidence `6129facb5471c56ea5b751cdebd102cb8d7790e3` as a bounded incremental repair. Review was finished before execution. This records committed source/log/hash reconciliation, not fresh reviewer execution or inspection of live objects.

Initial tracked state was clean at the accepted evidence commit. No Lean/Lake/checker was active and the universal lock was free. Approximately 19 GiB disk was free; the cgroup memory limit was 16 GiB with about 7.4 GiB used. All 486 accepted live source/object bindings and all 969 parent-manifest entries were rehashed. The independently rederived source-import closure has 39 affected modules and 447 unaffected modules.

Every compiler/checker invocation requires at least 4 GiB cgroup headroom and 4 GiB system MemAvailable before admission. Individual memory-admissions.jsonl observations are reconciled with receipts, and memory-admission-summary.json records their minima. This observes available memory without claiming a reservation or treating the supervisor disk gate as a memory gate. Both MemoryAdmission.py and the exclusive supervisor are unchanged from the accepted checkpoint. Individual supervisor preflights retain process/disk/memory observations.

All historical checkpoint trees and failed attempts remain unchanged, including prior execution gaps, aggregate-prefix OOM/sequencing qualification, theorem-count correction, evidence-writer-label correction and interruption records. No deleted/canceled ChatGPT workspace is accessed or recreated. No website or other paper is changed.

## Universal complete nested-output semantics

The rows recursion becomes explicit total `Nat.rec` on row count k. Its result is a function from starting row index to StoredRecords.Weights (a list of rational lists). The zero case returns []; the successor case prepends the unchanged `row bank start 0 n` and evaluates the tail at start+1. Explicit zero/successor equations are proved by `rfl`.

`LegacyEquivalence.lean` imports the exact hash-bound accepted implementation and proves equality of the complete nested output for every original bank and arbitrary natural width n, starting row i and count k. Induction generalizes i and applies the hypothesis at i+1. The replacement body is byte-identical to production. The theorem reports only **propext and Quot.sound**; no axiom or mathematical hypothesis is added. Before-source, replacement body, legacy object hashes and comparison-object hash are preserved. The comparison uses accepted legacy objects; new audit/replay use isolated current project outputs.

Width and row count are independent. There is no bound on the starting row relative to width, no square-matrix assumption and no restriction on bank validity, ordering, duplicates or signed rational payloads. A zero row count returns [] for every input. A zero width and positive count retains exactly k empty inner lists; it does not collapse to an empty outer list. Each emitted row starts at column zero, contains the unchanged full row output in increasing column order, and the starting row advances once per row, irrespective of width. No outer or inner reversal, filtering or truncation occurs. The accepted row preserves the existing first-match/reversed-key lookup behavior, zero/negative/fractional payloads and absent-cell zero. This is semantic equality, not a new physical-runtime claim about recursor evaluation.

Twenty fixtures compare complete nested rational lists, not lengths or flattened projections. Cases cover zero counts, zero widths retaining empty rows, empty banks, independent widths/counts, nonzero starting rows, a starting row of 10^20 and its successor, exact inner/outer ordering, signed/fractional sequences, missing cells, loops, reversed keys, duplicate-key priority, zero before later nonzero matches, large rational numerators and 16-row outputs. Universal zero/successor examples and metadata checks verify safety, totality, computability, explicit Nat.rec, no self-reference and no partial companion.

## Source scope

Two production Lean files change. In StoredOriginalWeightMatrix.lean, the entire prefix before rows is byte-identical, including repaired row, its equations, State and transition. The rows body is replaced and two explicit equations are added. All four pre-existing theorem statements remain unchanged; row_length is byte-identical. In rows_length, exactly one simp argument changes from rows to rows_succ.

In StoredOriginalWeightMatrixEncoding.lean, exactly one rewrite argument in rows_ofFn changes from rows to rows_succ. All three theorem statements are unchanged; row_ofFn and execute_encoded proof bodies are byte-identical. Both proof-interface adjustments were made before compilation based on the accepted analogous repairs. All other 484 closure source files remain unchanged, including all accepted lookup and typed-weight definitions.

## Complete affected rebuild and exhaustive audit

All 39 affected modules, including the aggregate, receive fresh strict compilation. The other 447 objects retain verified accepted source, direct-import and object hashes. Every affected state was removed before building so equal intermediate object bytes cannot skip required compilation. The evidence writer independently rederives imports and the closure from current source. Inherited historical receipts are not counted as fresh execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, remains unchanged. All nine dependency revisions are checked before each runner invocation, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Exact toolchain, manifest and supervisor hashes are recorded and reconciled. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, dependency change, warning suppression, blanket noncomputable conversion, alternate runtime or shim occurs.

The actual-owner audit and official resolver are unchanged apart from output-directory substitution. All project owners, recursive types/bodies, opaque values, inductive families and recursor rules remain covered. No generated name, partial root or remaining violation is filtered, exempted or allowlisted.

Fresh audit: 9169 actual-owner roots, 60588 recursive constants and 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only propext, Classical.choice and Quot.sound occur as axioms in the full closure. Exactly the rows companion disappears; all other 34 partial roots remain unchanged. The previously repaired row remains total and byte-identical. The strict audit exits 1 with 68 root/recursive findings. All generated-name and owner changes are recorded in owner-inventory-delta.json. This is a failing strict gate, not final acceptance.

## Singleton replay and raw evidence

The official resolver selects exactly one object/module for `LightEFTSpanners.StoredOriginalWeightMatrix`; the supervisor repeats singleton resolution under the universal lock. `leanchecker -v LightEFTSpanners.StoredOriginalWeightMatrix` passes with exactly one replay line. No aggregate-prefix replay occurs. Audit/replay LEAN_PATH contains isolated current project outputs, pinned packages and official toolchain without historical project fallback. Singleton replay does not discharge remaining partials; clean final exact-source validation is still required.

44 unique source-bound receipts have persisted supervisor preflights and individual memory-admission observations. They contain 534 submitted-source entries, exact argv/options, snapshots/hashes, lock inode, child PIDs, UTC/monotonic times, exits and reaping. Reconciliation verifies every snapshot, one lock inode, non-overlap and all children reaped. Concurrency is one. Zero anchored warning headers occur; hints and option names are not counted as warnings.

The only nonzero invocation is the unchanged exhaustive audit rejecting the remaining 34 partial roots. No compiler or fixture attempt failed in this checkpoint. The two known successor-equation proof adjustments were applied before compilation. No mathematical counterexample is claimed. The raw audit diagnostic and submitted source snapshots are preserved.

UUID directories preserve authoritative raw diagnostics and exact submitted sources; semantic-label logs are convenience copies. All historical failed attempts remain unchanged. `reconcile.py` is explicitly an evidence writer: it regenerates current derived evidence/chunks without invoking Lean/checker and verifies historical manifests without changing them. Its checks cover source/object/import bindings, exact closure, repaired row preservation, existing hypotheses, complete recursive audit, one-companion delta, singleton replay, memory admissions, receipts and historical preservation.

The complete recursive TSV is retained with 207 ordered row-aligned chunks and reconstruction hash in `audit-export/manifest.json`. Concatenate bytes in manifest order without extra headers or separators. The evidence manifest seals all checkpoint files except itself.

Entry points: `python checkpoints/light-eft-weight-rows-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-weight-rows-pilot-20261016/run.py pilot`, `build`, `audit`, `replay`; and noncompiling writer `python checkpoints/light-eft-weight-rows-pilot-20261016/reconcile.py`. Every compiler/checker call uses the unchanged exclusive supervisor and memory admission helper.

Publication uses additive source/evidence commits with `[skip ci]` after remote-state checks. Terminal observations record no compiler/checker, a free common lock, resources and repository CI statuses. The worker stops for sequential independent review.

Minimum observed admission headroom was 8,972,603,392 bytes in the cgroup and 17,433,104,384 bytes system MemAvailable.

Resumption qualification: an erroneous response reconciled an unrelated SCC checkpoint read-only. No SCC source, evidence, compiler state or remote was modified. The Light EFT partials were then reconciled against the accepted baseline; no additional compiler/checker execution was performed during publication.
