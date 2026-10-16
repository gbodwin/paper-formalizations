# StoredFlagSample.value total-recursor pilot

Tested source: `b1781be65eae837ae917d21c01e9cca319dae0bb`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

Fresh inspection confirmed the requested small list-recursion target and exactly nine affected modules. This bounded repair removes only `LightEFTSpanners.StoredFlagSample.value._unsafe_rec`: **47 → 46** partial roots, with none added. The unchanged strict complete-owner gate still fails. No CI is started. A clean final exact-source gate, Theorem 34, physical-runtime claims and whole-paper completion remain open. The worker pauses for independent review.

## Accepted baseline and live provenance

The parent reports independent acceptance of source `30e7f69cd16bedf914f3f754dd6877d57ddeafb2`, evidence `20c897ce4c9cf0c8690d24073729ca9c89d575cc`. The review inspected committed evidence only; it did not inspect live objects or perform fresh Lean execution. This worker independently rehashed all 486 baseline live objects and source bindings before reuse. Initial resource/process checks found about 21 GiB free disk, a 16 GiB memory limit, no compiler/checker and the universal lock free.

All accepted checkpoint manifests, raw failures and qualifications remain unchanged, including the Controller 494-preflight/495-receipt gap, historical aggregate-prefix OOM/internal parallelism, earlier theorem-count correction and reconciliation-writer-label correction. Only the current Light EFT worktree and its pinned dependencies were used; no canceled workspace was accessed.

## Complete semantics and unchanged hypotheses

`value : Input → List StoredEdges.Edge` now uses explicit total `List.rec`, returning [] on empty input and prepending the unchanged endpoint pair when its flag is true. The two explicit nil/cons equations are proved by `rfl`.

The universal legacy theorem proves full ordered-list equality against the preserved accepted implementation for **every original input list**. It depends on no axioms. The production and comparison replacement bodies are byte-identical. The final comparison receipt binds the theorem to the final production source, and the earlier successful comparison receipt and its metadata remain preserved.

`Input` is a list of `(ℕ × ℕ) × Bool`. No vertex-count, graph-validity, ordering, uniqueness, orientation or loop-free premise exists or has been added. “Malformed” inputs relative to an external graph—loops, repeated pairs, reversed pairs, arbitrary large endpoints or conflicting flags on repeated entries—are still accepted literally. True entries retain their order and multiplicity; false entries are discarded individually. There is no normalization, deduplication, sorting or validation. Negative endpoints and non-Boolean flags are outside the original input type, not cases newly excluded by this repair.

Only the value definition and two equations are added/replaced. The existing `value_length` proof changes one simp argument to `value_cons`; the downstream `value_map` proof makes the same one-argument change. All three original theorem headers in StoredFlagSample and all three in StoredFlagSampleExecutable are byte-identical. All other declarations and definitions in those files are unchanged, as are the other 484 closure source files. In particular, graph-encoding and probabilistic theorem hypotheses are preserved.

Fresh metadata checks confirm safe, total, computable status, explicit List.rec, no self-reference and no partial companion. Fifteen complete-list fixtures pass: empty input, single true/false flags, all-false lists, loops at zero and nonzero endpoints, duplicate multiplicity, reversed-pair identity, mixed flags and order, and endpoints larger than a machine word. Universal nil/cons examples also pass. The endpoint-pair data are natural numbers; no rational or physical-runtime claim is introduced.

## Exact nine-module rebuild

The isolated `.lake/flag-value-pilot/lib/lean` began with 486 verified accepted object copies. The import graph identifies exactly:

- LightEFTSpanners.StoredFlagSample
- LightEFTSpanners.StoredFlagSampleExecutable
- LightEFTSpanners.StoredFlagBatch
- LightEFTSpanners.StoredFlagBatchTrace
- LightEFTSpanners.StoredFlagSampleEncoding
- LightEFTSpanners.StoredFlagBatchExecutable
- LightEFTSpanners.StoredFlagSampleProbability
- LightEFTSpanners.StoredFlagBatchProbability
- LightEFTSpanners (aggregate compilation only)

All nine affected states were invalidated before the build, and all nine modules received successful fresh strict compilation regardless of intermediate object equality. The remaining 477 objects retain accepted source, direct-import and object hashes. `source-object-provenance.json` explicitly distinguishes fresh compilation and inherited objects.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine dependency revisions remain pinned, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Strict commands use `-j1 -DautoImplicit=false -DwarningAsError=true`. Audit/replay search paths use the isolated outputs, pinned packages and official toolchain, with no old project fallback. No dependency update, default Lake build, runtime shim, warning suppression or blanket noncomputable conversion occurs. This remains incremental validation, not a clean final dependency rebuild.

## Exhaustive audit and singleton replay

The full actual-owner audit and official target resolver are unchanged except output-directory substitution. No roots or generated names are filtered. Recursive types/bodies, opaque values, inductive families and recursor rules retain their existing coverage.

Fresh audit: 9241 actual-owner roots, 60660 recursive constants, 48 opaque bodies, zero unsafe project roots and zero aggregate-owned declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms in the full closure. Exactly the value partial companion disappears; all other 46 partial roots remain unchanged. Strict audit exits 1 with exactly 92 findings, one root and one recursive finding per partial. This is **not** a passing strict gate. The complete generated-name/actual-owner delta is preserved in `owner-inventory-delta.json`: ten roots disappear and three appear, comprising two explicit equations and one replacement proof helper; there are no actual-owner changes.

The official resolver selects exactly one module/object for `LightEFTSpanners.StoredFlagSample`, and the supervisor repeats filesystem resolution under the universal lock. Official `leanchecker -v LightEFTSpanners.StoredFlagSample` passes with exactly one replay line. No aggregate-prefix replay is invoked. `LEAN_SYSROOT` identifies the official toolchain. A successful replay does not discharge the unchanged no-partial audit.

## Preserved attempts and evidence

All 18 source-bound UUID receipts have persisted preflights, exact commands/options, source snapshots/hashes, lock inode, child PIDs, UTC/monotonic timing and reaping results. There are 511 submitted-source entries. Reconciliation verifies non-overlap, one lock inode and all children reaped. No warning headers occur. Diagnostic classification counts anchored source headers; hints are not warnings and strict-linter findings promoted to errors remain recorded as errors.

Four nonzero Lean attempts are preserved with their raw diagnostics and source snapshots:

1. The initial production compilation unfolded the recursor past the form used by the length induction hypothesis. Its proof now uses the explicit cons equation. The arithmetic tactic's possible assignment described an unconnected elaborated goal, not a counterexample to `value_length` or to a paper theorem.
2. The first fixture file lacked the final bracket closing the list of checks; the test syntax was repaired.
3. The first downstream compilation unfolded value past its map induction hypothesis. That proof now uses the same explicit cons equation.
4. The strict exhaustive audit rejects the remaining 46 partial roots.

The initial and final legacy proof receipts are both preserved, with initial metadata copied separately before the final-source invocation. UUID directories remain authoritative; semantic-label logs are convenience copies. No accepted historical evidence or failed attempt was discarded.

The evidence writer `reconcile.py` explicitly documents that it rewrites current derived JSON files and audit chunks; it is not filesystem-read-only and does not execute Lean/checker. `RECONCILIATION_SCOPE.md` retains the additive correction to the historical label. Historical checkpoint contents are verified without modification. The full TSV is preserved alongside 207 ordered row-aligned chunks and their reconstruction hash. Concatenate listed bytes without extra separators or headers.

Entry points are `python checkpoints/light-eft-flag-value-pilot-20261016/legacy_compare.py` and `python checkpoints/light-eft-flag-value-pilot-20261016/run.py pilot`, `build`, `audit`, or `replay`. `python checkpoints/light-eft-flag-value-pilot-20261016/reconcile.py` regenerates derived evidence before sealing. All compiler/checker invocations use the unchanged universal supervisor.

Publication is additive with `[skip ci]`. The worker stops with no compiler/checker running and the lock free, awaiting independent review. No CI or website changes occur.
