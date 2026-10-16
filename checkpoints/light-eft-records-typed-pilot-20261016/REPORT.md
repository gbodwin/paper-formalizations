# StoredOriginalCandidateRecords.typedValue total-recursor pilot

Tested source: `5f15ce94d6728e534beb0bdb009d3929f78ed357`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

Fresh inspection identified the remaining same-file record recursion and its complete 14-module transitive affected closure. This separate bounded repair removes exactly `LightEFTSpanners.StoredOriginalCandidateRecords.typedValue._unsafe_rec`: **45 → 44** partial roots, with none added. The unchanged strict all-owner gate still fails. CI remains off. A clean final exact-source gate, Theorem 34, physical-runtime claims and whole-paper completion remain open. This checkpoint pauses for independent review.

## Accepted baseline and current bindings

The parent reports independent acceptance of source `4f910953931b2398a74b96c518418f0aaf0be16b`, evidence `342dd6ae78c4771111b989f966467ef0af04b5dd`. That review inspected committed source/evidence, not live objects or fresh execution. This worker independently rehashed all 486 baseline source/object bindings before reuse. Initial checks found a clean worktree, no live compiler/checker, the universal lock free, about 21 GiB free disk and a 16 GiB memory limit.

All accepted checkpoint contents and qualifications remain unchanged, including earlier failures, the Controller 494-preflight/495-receipt gap, historical aggregate-prefix OOM/internal parallelism, earlier theorem-count correction and reconciliation-writer-label correction. The historical-tree inventory compares all existing checkpoint entries against the parent commit. No canceled workspace or other paper was accessed.

## Unrestricted ordered record semantics

For arbitrary n, exclusion list Q, typed candidate-draw bank and candidate list xs, the function removes every candidate x whose undirected edge belongs to `StoredSample.edgeSet Q`. For each survivor it emits the record containing **the original ordered endpoint pair x** and the complete result of the already accepted first-match candidate-draw lookup. The explicit total List.rec replacement has exactly these nil/cons equations, both proved by `rfl`.

The universal legacy theorem proves equality of the full `List (StoredForestBank.TypedInput n)` against the actual hash-bound accepted implementation. Both fields of every record, list ordering and multiplicity are covered. The replacement body is byte-identical to production. The theorem uses only `propext`, `Classical.choice` and `Quot.sound`.

No graph-validity, uniqueness, canonical orientation, sorted-input, nonempty-bank or payload-validity premise is added. Repeated and reversed entries in Q have the same undirected membership meaning. Every matching occurrence in xs is excluded. Surviving duplicates remain duplicated, and reversed survivor pairs retain their original orientation. Missing or empty lookup payloads still produce an output record with an empty bank; they do not cause another filtering step. Duplicate/reversed lookup keys retain accepted first-match priority. Nested bank indices, empty draw lists, loops, repeated/reversed edges and all payload order/multiplicity are retained without normalization or merging.

Endpoints remain Fin n as in the original domain; arbitrary natural bank indices remain unrestricted. The n=0 boundary is an actual valid call `typedValue (n:=0) [] [] [] = []`, with no fabricated endpoint or query. Singleton-loop inputs are tested both excluded and retained. This is output equivalence; no additional runtime claim about evaluating the new recursor is introduced. The existing executable transition/value definitions and trace contracts remain unchanged.

Only this typedValue definition and two explicit equations change in StoredCandidateDrawEncoding. The entire accepted StoredCandidateDrawLookup namespace is byte-identical. All four existing theorem statements and bodies in the file—including both namespace-qualified `value_encoded` theorems and the accepted lookup equations—remain unchanged. The comment-aware scanner is applied separately to both explicit namespace blocks to distinguish repeated unqualified theorem names.

One downstream proof argument changes: `StoredOriginalCandidateRecords.typedValue_filter` in StoredCandidateBankRepresentation uses `typedValue_cons` instead of unfolding `typedValue`. All three existing theorem headers and every definition in that supporting file are unchanged; the remaining 484 closure source files are byte-identical. This is a proof-interface adjustment, not a changed mathematical assumption.

## Boundary and metadata checks

Fresh metadata confirms the target is safe, total and computable, uses explicit List.rec, has no self-reference and has no partial companion. Universal nil/cons examples compile. Seventeen executable fixtures compare entire output record lists: zero/singleton vertices, empty input, missing/empty payloads, Q membership under reversal and duplication, all matching occurrences removed, survivor order/multiplicity/orientation, loop handling, first-match duplicate bank entries and unrestricted nested payloads. The test file derives a structural DecidableEq instance locally to that test module, comparing both record fields; no production type or instance is changed.

## Complete affected rebuild and inherited provenance

The isolated `.lake/records-typed-pilot/lib/lean` starts from 486 verified accepted object copies. `affected-closure.json` records the exact 14-module closure rooted at StoredCandidateDrawEncoding, including its downstream sorted-candidate, original-caller/execution, representation, guarantee modules and the aggregate. Every affected state was removed before rebuilding, forcing fresh compilation even when intermediate object bytes stayed identical. All 14 modules strictly compile. The other 472 objects retain accepted source, direct-import and object hashes. `source-object-provenance.json` distinguishes fresh from inherited objects; historical receipts are not counted as new executions.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine pinned dependencies remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Strict compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. Audit/replay search paths use the isolated outputs, pinned packages and official toolchain, without old project fallback. No default Lake build, dependency update, runtime shim, warning suppression or blanket noncomputable conversion occurs. This remains incremental validation, not a clean final dependency rebuild.

## Unchanged exhaustive audit and guarded replay

The complete actual-owner audit and official resolver are copied unchanged except output-directory substitution. All owners and recursive types/bodies, opaque values, inductive families and recursor rules retain their existing coverage. No roots, generated names or remaining partials are filtered or allowlisted.

Fresh audit: 9227 actual-owner roots, 60646 recursive constants, 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms in the full closure. Exactly the target partial companion disappears; all other 44 partial roots remain unchanged. Strict audit exits 1 with 88 findings, one root and one recursive finding per remaining partial. This is **not** a passing strict gate. `owner-inventory-delta.json` preserves the complete delta: nine generated roots disappear and the two explicit equations appear, with no actual-owner changes.

The official resolver selects exactly one module/object for LightEFTSpanners.StoredCandidateDrawEncoding; the supervisor repeats filesystem resolution under the universal lock. Official `leanchecker -v LightEFTSpanners.StoredCandidateDrawEncoding` passes with exactly one replay line. `LEAN_SYSROOT` points to the official toolchain. No aggregate-prefix replay occurs. Singleton replay does not discharge the full no-partial gate.

## Receipts, diagnostics and review exports

All 21 source-bound UUID receipts have persisted preflights, exact commands/options, source snapshots/hashes, lock inode, child PIDs, UTC/monotonic timing and reaping results. There are 512 submitted-source entries. Reconciliation verifies a single lock inode, strict non-overlap and every child reaped. No warning headers occur; diagnostics are counted by anchored source headers rather than hints or option text.

Three nonzero Lean attempts are preserved with raw diagnostics and submitted source:

1. The first fixture file used anonymous record-constructor notation without sufficient expected type information. Explicit typed constructors repaired the test syntax; both record fields are still tested.
2. The downstream filter proof unfolded the recursor past the form used by its induction hypothesis. Using the explicit cons equation repairs the proof without changing its statement or suppressing the strict unused-simp diagnostic.
3. The unchanged exhaustive audit rejects the remaining 44 partial roots.

All historical failures remain untouched. UUID attempt directories are authoritative; semantic-label logs are convenience copies. The evidence writer `reconcile.py` documents that it rewrites derived JSON/chunks and does not execute Lean/checker; it is not filesystem-read-only. The additive historical label correction is preserved in RECONCILIATION_SCOPE.md.

Reconciliation checks all 486 source/object/import bindings, exact affected closure, unchanged theorem headers/bodies and the single supporting proof adjustment, receipts/preflights, snapshots, complete recursive closure, exact one-companion removal, singleton resolution and preserved historical manifests. The full dependency TSV is retained alongside 207 ordered row-aligned chunks with per-chunk and reconstruction hashes. Concatenate listed bytes without additional separators or headers.

Entry points: `python checkpoints/light-eft-records-typed-pilot-20261016/legacy_compare.py`; `python checkpoints/light-eft-records-typed-pilot-20261016/run.py pilot`, `build`, `audit`, or `replay`. `python checkpoints/light-eft-records-typed-pilot-20261016/reconcile.py` regenerates derived evidence before sealing. All compiler/checker invocations use the unchanged exclusive supervisor.

Publication uses additive source/evidence commits with `[skip ci]`. The worker stops with no compiler/checker running and the universal lock free, awaiting independent review. No CI, website change or broader paper claim is introduced.
