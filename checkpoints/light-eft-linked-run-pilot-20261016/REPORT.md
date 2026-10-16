# LinkedDistance.run total-recursor pilot

Tested source: `30e7f69cd16bedf914f3f754dd6877d57ddeafb2`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

The bounded controller repair removes exactly `LightEFTSpanners.LinkedDistance.run._unsafe_rec`, with none added: **48 → 47** partial roots. The unchanged strict complete-owner gate still fails. CI remains off. This checkpoint pauses for independent review. A clean final exact-source gate, Theorem 34, physical-runtime claims and whole-paper completion remain open.

## Accepted baseline and preservation

The parent reports independent acceptance of source `0ddd75593fb251ec42bfb04d9b7aa0e593eead2e`, evidence `d12c2ec285c9a34341345c641948afa774395807`, including all 207 chunks and the exhaustive audit. That review reconciled source/log/hash evidence; it did not run Lean or inspect live object bytes. This worker independently verified all 486 baseline live object hashes before reuse. All historical checkpoint manifests remain byte-identical, including failures, the Controller 494-preflight/495-receipt qualification and historical aggregate-prefix OOM/internal-parallelism violation. The earlier voting-work theorem-count correction remains preserved.

The saved environment was verified ready before work began. Initial checks found no compiler/checker, the universal lock free, about 21 GiB free disk and a 16 GiB memory limit. Only the current Light EFT paper was used; no canceled workspace or other-paper proof development was accessed.

## Exact full-state semantics

`LinkedDistance.run` is fuel-bounded iteration of the unchanged `transition` function. Its explicit `Nat.rec` replacement returns the input state at zero fuel. At successor fuel, a terminal `none` transition returns the same state immediately; a `some t` transition applies the previous fuel function to t. This preserves the entire controller state, not merely a Boolean result or termination property. The zero/successor equations are both proved by `rfl`.

`LegacyEquivalence.lean` imports the actual hash-bound accepted implementation and proves universal equality of the entire `State` for every size, matrix, source/target register, rational budget, fuel and initial state. The replacement body is byte-identical to production. There are no nonnegativity, shape, graph-encoding, valid-register or reachable-state assumptions. Ragged/empty matrices and out-of-range registers remain admissible. This fuel-level statement does not strengthen the separate graph-encoding or nonnegative-weight hypotheses of `execute_correct`.

Only the run definition and its two new equations are changed. In `Executes.run_eq`, one simp argument changes from direct `run` unfolding to `run_succ`. In `LinkedDistanceExecutable.run_add`, the terminal case applies existing `run_terminal` directly. All three existing theorem headers in LinkedDistanceMachine and all five in LinkedDistanceExecutable are unchanged; every other production definition is byte-identical. The other 484 closure source files are unchanged. This is a proof-interface repair, not a changed mathematical claim.

Fresh metadata confirms run is safe, total and computable, uses Nat.rec, has no self-reference and has no partial companion. Universal examples check its equations. All 27 executable full-state fixtures pass: terminal true/false states, every State constructor, exhausted fuel, empty/ragged inputs, out-of-range lookups, negative/fractional arithmetic, and complete finite-fuel runs. In particular, finite fuel can stop at an intermediate lookup state, and additional fuel leaves terminal states unchanged. No rational bit-runtime claim is introduced.

## Full affected rebuild and provenance

The isolated `.lake/linked-run-pilot/lib/lean` began with 486 verified accepted object copies. The import graph identifies the full **189-module transitive affected closure**. All affected states were removed before the build, forcing each dependent to compile even if intermediate object bytes remained unchanged. All 189 modules were freshly strictly compiled, including the aggregate. The remaining **297 objects** are inherited with unchanged source, direct-import and object hashes. `source-object-provenance.json` distinguishes these cases explicitly.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine pinned dependencies remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Compiles use `-j1 -DautoImplicit=false -DwarningAsError=true`. No dependency update, default Lake build, runtime shim, warning suppression or blanket noncomputable conversion is used. New audit/replay paths contain the isolated outputs, pinned dependencies and official toolchain without old project fallback. This remains incremental verification, not a clean final dependency rebuild.

## Unchanged exhaustive audit and guarded replay

The complete actual-owner audit and official target resolver are copied unchanged except output-directory substitution. No roots or generated names are filtered. Recursive types and bodies, opaque values, inductive families and recursor rules retain their existing coverage.

The fresh audit contains 9248 actual-owner roots, 60667 recursive constants and 48 opaque bodies. Only `propext`, `Classical.choice` and `Quot.sound` occur as axioms. There are zero unsafe project roots and zero aggregate-owned declarations. Exactly the run partial companion disappears; the other 47 partial roots are unchanged and no new partial appears. Strict audit exits 1 with exactly 94 findings, one root and one recursive finding per remaining partial. This is **not** a passing strict gate.

`owner-inventory-delta.json` records every generated-root and actual-owner change: 12 roots disappear and five appear; the generated `run.eq_1` changes actual owner from LinkedDistanceMachine to LinkedDistanceExecutable. All are included under their actual owners without filtering. The official resolver selects exactly one object for `LightEFTSpanners.LinkedDistanceMachine`; the supervisor repeats the filesystem resolution under the lock. Official `leanchecker -v LightEFTSpanners.LinkedDistanceMachine` passes with exactly one replay line. `LEAN_SYSROOT` is the official toolchain. No aggregate-prefix replay or internally parallel multi-target replay occurs. Replay does not itself certify the all-owner no-partial condition.

## Receipts and failed attempts

All 198 unique source-bound receipts have persisted preflights, exact commands/options, source snapshots/hashes, lock inode, child PIDs, UTC/monotonic timestamps and reaping results. There are 691 submitted-source entries. Reconciliation verifies a single lock inode, strict non-overlap and every child reaped. Zero warning headers occur; diagnostics are counted by anchored source headers, not hints or option names. Strict-linter findings promoted to errors remain errors in the raw logs.

Four nonzero Lean attempts are preserved with raw diagnostics and exact submitted sources:

1. Initial machine compilation unfolded run past the form used by its induction hypothesis; the proof now uses the explicit successor equation.
2. Initial boundary fixtures used ambiguous dotted State constructors; explicit constructor names repaired the test syntax.
3. Initial downstream executable compilation unfolded run before applying its existing terminal theorem; the terminal branch now invokes that theorem directly.
4. The unchanged strict audit rejects the remaining 47 partial roots.

The initial legacy proof is preserved. After the production proof-interface adjustment, a second successful legacy invocation binds the comparison to the final production source; both receipts remain, and the initial comparison metadata is retained separately. Semantic-label logs are convenience copies; UUID attempt directories are authoritative. No failed attempt or accepted historical evidence was discarded.

## Reconciliation side effects and review exports

**`reconcile.py` is not filesystem-read-only.** It does not execute Lean/checker, but rewrites this checkpoint's derived JSON files, audit chunks and chunk manifest. Its new docstring and `RECONCILIATION_SCOPE.md` correct the historical misleading label additively. Historical scripts/reports/manifests remain untouched. A reviewer seeking read-only verification should inspect saved artifacts and hashes, not run this evidence writer.

The reconciliation checks all 486 source/object/import bindings, full affected-closure rebuild, exact statement/proof-interface changes, singleton resolution, receipt/preflight bijection, source snapshots, recursive closure, exact one-companion removal and historical manifests. The complete TSV remains available, exported into 207 ordered row-aligned chunks with per-chunk and reconstruction hashes. Concatenate listed bytes without extra separators or headers.

Entry points: `python checkpoints/light-eft-linked-run-pilot-20261016/legacy_compare.py`, and `python checkpoints/light-eft-linked-run-pilot-20261016/run.py pilot`, `build`, `audit`, or `replay`. The evidence-regeneration command is `python checkpoints/light-eft-linked-run-pilot-20261016/reconcile.py`. All compiler/checker commands run through the unchanged exclusive supervisor; historical aggregate-prefix commands must not be run.

Publication uses additive source/evidence commits with `[skip ci]`. No CI or website changes are made. The worker stops with no compiler/checker running and the universal lock free, awaiting independent review before another repair.
