# LinkedDistance.rounds total-recursor pilot

Tested source: `0ddd75593fb251ec42bfb04d9b7aa0e593eead2e`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

The bounded rounds repair removes exactly `LightEFTSpanners.LinkedDistance.rounds._unsafe_rec`, with none added: **49 → 48** partial roots. The unchanged strict complete-owner gate still fails. No CI is started. This checkpoint pauses for independent review; a clean final exact-source gate, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and continuity

The parent reports independent acceptance of source `df314468ce8acd53149d33c283228c98b5b6d4e5`, evidence `002de07066524a54d1f0ad84a9e4d3054ac450ab`. That review reconciled source/log/hash evidence; it did not rerun Lean or inspect live objects. Here the worker independently rehashed all 486 baseline objects before reuse and preserved all prior checkpoint manifests. Historical Controller 494-preflight/495-receipt and aggregate-prefix OOM/internal-parallelism qualifications remain unchanged. The earlier voting-work theorem-count correction remains additive.

Work resumed from the preserved uncommitted rounds repair and its successful legacy-equivalence receipt after the parent explicitly resolved a context-selection ambiguity to Light EFT only. The intervening SCC response was an incorrect task selection, not this task's result; it performed read-only reconciliation and no compilation or edits. No SCC source or evidence was changed. The resumed environment was verified connected. This checkpoint records only Light EFT proof work.

## Exact semantics

`rounds` now uses explicit total `Nat.rec` with result type `List Cell → List Cell`. Its zero step returns the entire input list. Its successor applies the previous round function to `rows d M d`. The explicit zero and successor equations are proved by `rfl`.

For every optional rational matrix M, arbitrary natural k and arbitrary cell list d, the full output list equals the preserved old implementation. There are no shape, graph-encoding, nonnegativity or reachability premises. Empty and ragged matrices remain admissible, and the existing truncation behavior is preserved. Negative cycles can decrease entries in later rounds; there is no clamp to zero.

`LegacyEquivalence.lean` defines the byte-identical replacement body in a comparison namespace and imports the hash-bound accepted old kernel. Its universal full-list equality strictly compiles. The pre-resumption receipt and source snapshots are retained unchanged. The legacy input metadata inherited the phrase “full-pair equality”; the actual theorem is full **list** equality, as its preserved source shows. That descriptive label is not a claim that this output has a counter component.

Only the rounds definition and its two new equations change. All five pre-existing theorem statements and their proofs in LinkedDistanceKernel remain byte-identical, as does every other declaration in that file. All 485 other closure source files are unchanged, including the downstream trace and refinement proofs. No hypothesis or mathematical coverage claim changes.

Fresh metadata checks establish safe, nonpartial, computable status, explicit Nat.rec, no self-reference and no rounds partial companion. All 17 executable full-list fixtures pass: zero rounds, empty inputs, empty rows, ragged truncation, missing cells, negative and fractional values, a negative cycle through three rounds, and nonnegative cases. These test actual list inputs, including empty lists, without fabricating a target vertex.

## Production rebuild and object provenance

The isolated `.lake/rounds-pilot/lib/lean` started with 486 hash-verified accepted objects. The source-derived import graph identifies all **190 transitively affected modules**. Their states were invalidated before rebuilding so unchanged intermediate object bytes could not skip downstream recompilation. All 190 received successful fresh strict compilations, including the aggregate. The other **296 objects** retain accepted source, direct-import and object hashes and are explicitly marked inherited in `source-object-provenance.json`.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine dependency revisions remain pinned, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Production compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No default Lake build, runtime shim, dependency change, warning suppression or blanket noncomputable conversion is used. Audit/replay search paths use only the isolated project objects, pinned packages and official toolchain, without old project fallback. This is incremental validation, not a clean final dependency rebuild.

## Unchanged audit and singleton replay

The full actual-owner audit and official target resolver are unchanged except output-directory substitution. The audit traverses all actual project owners and recursive types/bodies, including opaque values and inductive/recursor declarations. It does not filter roots or generated names.

The fresh audit records 9255 actual-owner project roots, 60674 recursive constants and 48 opaque bodies. Exactly the rounds companion disappears. The other 48 partial roots are unchanged, with no new partials, zero unsafe project roots and zero aggregate-owned roots. Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms. The strict audit exits 1 with exactly 96 findings: one root and one recursive finding per remaining partial. This is **not** a passing strict gate.

The complete generated-name and owner delta is in `owner-inventory-delta.json`. No declaration is omitted because its generated name or actual owner changed.

The official resolver selects exactly one module/object for `LightEFTSpanners.LinkedDistanceKernel`. The unchanged supervisor repeats the filesystem check under the universal lock. Official `leanchecker -v LightEFTSpanners.LinkedDistanceKernel` succeeds with exactly one replay line. `LEAN_SYSROOT` points to the official toolchain. No aggregate-prefix replay is invoked. Official replay does not itself discharge the complete no-partial audit.

## Receipts, diagnostics and review

All 195 unique source-bound receipts have persisted preflights, exact commands/options, submitted source snapshots/hashes, lock inode, child PIDs, UTC/monotonic timing, raw diagnostics and reaping results. Reconciliation verifies non-overlap, a single lock inode, all children reaped and all snapshots. There are 685 submitted-source entries. Warning classification counts anchored diagnostic headers, not hints or option text. All successful attempts have zero warnings and errors. The sole nonzero Lean attempt is the expected strict audit rejection; its complete raw output is preserved. No prior failed attempt is removed.

`reconcile.py` checks the full affected closure, all 486 source/object/import bindings, unchanged statements, exact one-companion reduction, complete recursive closure, singleton resolution and replay, all receipts/preflights and prior evidence. The complete TSV is preserved and exported into 207 ordered row-aligned chunks with a reconstruction hash. Concatenate listed chunk bytes without separators or repeated headers.

Entry points: `python checkpoints/light-eft-rounds-pilot-20261016/legacy_compare.py` for the preserved comparison; `python checkpoints/light-eft-rounds-pilot-20261016/run.py pilot`, `build`, `audit`, and `replay` for sequential checks. Read-only reconciliation is `python checkpoints/light-eft-rounds-pilot-20261016/reconcile.py`. Do not run historical aggregate-prefix commands.

Publication uses additive source/evidence commits with `[skip ci]`. No automatic CI, website changes or other-paper proof development occurs. The worker stops with no compiler/checker running and the universal lock free for independent review.
