# RationalDistance.table total-recursor pilot

Tested source: `df314468ce8acd53149d33c283228c98b5b6d4e5`. Branch: `light-eft-spanners-checkpoints`. Exact binding: `evidence/source-binding.json`.

The bounded table repair is validated: exactly `LightEFTSpanners.RationalDistance.table._unsafe_rec` is removed, with none added, **50 → 49** partial roots. The unchanged strict complete-owner gate still fails. No CI is started. The worker pauses for independent review before any further definition is repaired. A clean final exact-source gate, Theorem 34 and whole-paper completion remain open; no physical-runtime claim is made.

## Accepted baseline and preserved qualifications

The parent reports independent acceptance of source `ea5017d9cbe674374bac972136f995a7248a9111`, evidence `adc1e297eae9e01e83391bee5a47f326f5329d91`, including full outputs/counters and the additive declaration-parser correction. This records source/log/hash reconciliation, not new reviewer execution. All prior evidence remains byte-identical, including the corrected eight-statement count for the earlier voting-work pilot, its original mistaken artifact, the Controller 494-preflight/495-receipt qualification, and the historical aggregate-prefix OOM/internal-parallelism violation.

Validation remains incremental and uses pinned dependency caches plus hash-bound unaffected project objects. A clean final exact-source validation is still required. The broader affected-module rebuild here does not remove that qualification.

## Exact definition and mathematical semantics

`table` now uses explicit total `Nat.rec` with the same initial vector and the same `step G w` successor. Its type, target argument, rational weights and arbitrary natural round count are unchanged. No nonnegativity premise is added. The explicit `table_zero` and `table_succ` equations are both proved by `rfl`. All five pre-existing theorem statements in RationalDistanceTable, including `below_table_iff`, are byte-identical. Its proof uses the explicit equations.

`below_table_iff` remains the same bounded-walk statement: a vector entry is below b exactly when a walk to the target has length at most k and rational cost at most b. Negative weights are allowed. No new claim about unrestricted shortest distances is introduced.

The only supporting source change is one simp argument in `LinkedDistanceRefinement.initial_encoded`: `table` becomes `table_zero`. Its statement and every definition in that file remain unchanged; all its existing theorem headers are checked. The other 484 closure source files are byte-identical to the accepted source. Only the table definition is repaired; source/import/object provenance is retained for every dependent module.

`LegacyEquivalence.lean` imports the actual preserved old implementation from the accepted object set and defines the byte-identical replacement body in a comparison namespace. Its universally quantified theorem proves equality of the entire vector for every graph, decidable adjacency, rational weight function, target and round count, without a nonnegativity assumption. The old source snapshot and all 486 old object hashes are checked before compilation. The proof strictly compiles with only `propext`, `Classical.choice` and `Quot.sound`.

The fresh metadata check confirms safe, nonpartial, computable status, explicit Nat.rec, absence of self-reference and absence of the table partial companion. Twelve full table-vector fixtures pass: zero rounds, unreachable vertices, positive/zero weights, negative weights over one through four rounds, a different target, fractional negative weights, and singleton graphs. Negative-cycle fixtures verify that target entries can decrease below zero at later rounds; no zero clamp or nonnegativity restriction was introduced.

Two additional executable fixtures check `step` and the same recurrence on an empty vector. The unchanged table type requires `target : Fin n`; at n=0 no actual target exists. A separate Lean example discharges that impossible-target case by `Fin.elim0`. No nonexistent target is fabricated, and the empty recurrence fixtures are not represented as actual Fin-0 table calls. All 14 executable fixtures pass.

## Full transitive affected-module validation

The isolated `.lake/table-pilot/lib/lean` began with 486 verified accepted object copies. `affected-closure.json` records the complete import graph and the **195-module transitive dependent closure** of RationalDistanceTable. Every module in that closure was strictly recompiled, even when intermediate object bytes were unchanged. This prevents unchanged immediate-import bytes from being treated as sufficient validation of downstream proofs after generated equations change.

The other **291 objects are inherited**, with unchanged source, direct-import and object hashes. `source-object-provenance.json` explicitly distinguishes newly compiled and inherited objects. The closure has 195 new successful module compilations; 196 successful compile invocations are retained because an intermediate aggregate compile preceded the full transitive rebuild. The final aggregate was compiled again after all affected modules. No historical receipt is counted as a new execution.

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and all nine pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Strict compiles use `-j1 -DautoImplicit=false -DwarningAsError=true` and successful final compiles emit zero warning headers. The new audit path has no old project-directory fallback. No default Lake build or dependency update is used.

## Fresh complete audit and guarded replay

The complete actual-owner audit and official resolver are unchanged except output paths. All owners and recursive types/bodies, opaque values, inductive families and recursor rules remain covered. The fresh result is **9,262 actual-owner roots, 60,681 recursive constants and 48 opaque bodies**. Only the standard three axioms occur; there are zero unsafe project roots and zero aggregate-owned declarations.

Exactly the table companion disappears. The other **49 partial roots** are unchanged and none is added. The strict audit exits 1 with **98 findings**, one root and one recursive finding per remaining partial. This is not a passing strict gate. No generated name is filtered or allowlisted.

The full name delta removes 11 generated roots and adds four: the two explicit equations and two replacement generated proof helpers. Actual-owner changes are also recorded: `RationalDistance.step.congr_simp` moves from RationalDistanceTable to LinkedDistanceRefinement, and `RationalDistance.table.eq_1` moves from RationalDistanceTable to RationalDistanceWork. These lazily generated declarations are included under their actual owners in the complete audit; they are not extra handwritten definition repairs or omissions.

The official resolver selects exactly one module/object for `LightEFTSpanners.RationalDistanceTable`. The supervisor repeats the filesystem check under the universal lock. Official `leanchecker -v LightEFTSpanners.RationalDistanceTable` passes with exactly one replay line. `LEAN_SYSROOT` names the official toolchain. No aggregate-prefix or internally parallel multi-target replay is started.

## Preserved attempts and review evidence

All **203** new source-bound UUID receipts have persisted process/resource preflights with matching UUID and hash, source snapshots, full commands/options, lock inode, PIDs, UTC/monotonic times and child reaping. Reconciliation verifies non-overlap and reaping. Three nonzero attempts are preserved:

1. The first empty-vector recurrence fixture needed an explicit Nat.rec motive during elaboration; production table compilation had already passed. The test-only type annotation repaired it.
2. The first LinkedDistanceRefinement compile reported an unused simp argument after direct unfolding of table changed. Its one-token switch to the explicit zero equation passes strict lint without suppression.
3. The final strict audit rejects the remaining 49 partial roots under the unchanged policy.

Raw diagnostics and submitted sources remain in the UUID directories; convenience logs do not replace them. Warning counts use anchored source diagnostic headers, not hints or option names. No source proof is accepted from a failed attempt.

`reconcile.py` checks source/object/import hashes, every transitive dependent's fresh compile, full recursive closure, the exact one-companion reduction, owner changes, singleton resolution, source-bound receipts/preflights, statement preservation and prior evidence. The full dependency TSV is retained and exported into **207** ordered row-aligned chunks with per-chunk and reconstruction hashes. Concatenate bytes in listed order without extra headers or separators.

Publication is additive with `[skip ci]`. No warning suppression, runtime shim, extra hypothesis, blanket noncomputable change, website change, other-project proof work or automatic CI is used. The worker is left idle for independent review.
