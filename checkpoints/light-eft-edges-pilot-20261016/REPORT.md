# ExecutableVoting.edges explicit List.rec pilot

Tested source: `05d0ab325ee7b4e1dd7fc84713f2676a7f311936`. Exact binding: `evidence/source-binding.json`. Branch: `light-eft-spanners-checkpoints`.

Bounded `ExecutableVoting.edges` pilot verified: the unchanged complete strict gate still fails on 55 remaining partial roots. The exact partial-set difference is removal of `LightEFTSpanners.ExecutableVoting.edges._unsafe_rec` only. No CI is authorized while the strict all-owner gate fails. No whole-paper completion or runtime-complexity claim is made; Theorem 34 remains open.

## Accepted baseline and historical qualifications

The parent reports independent acceptance of Controller pilot source `5e9df7b0ec4f9b6cb22c313fd82159a777035f41`, evidence `21e2f76d12090baf32e29e13932c113edce44788`: 2,725 manifest entries, 208 chunks and 495 receipts. This records source/log/hash reconciliation, not new reviewer execution. Its complete audit retained 56 partial roots. The historical qualification remains: 494 persisted preflights for 495 receipts; the legacy comparison checked processes/resources but did not persist that observation. The older aggregate-prefix OOM and sequencing violation remain preserved, not rehabilitated.

All previous evidence remains byte-identical. The new common supervisor persists process and resource observations under the universal lock for every invocation, including comparison proofs. Each preflight has the same UUID as its receipt, and its hash is embedded in that receipt. The current `scripts/LightEFTSequential.py` and this checkpoint's supervisor are identical. Historical scripts and evidence are not rewritten.

## Repair and equality

The production definition uses explicit `List.rec Q (fun e _ E => if h ≤ (votes … E e).card then insert e E else E)`. Its type is unchanged. Explicit `edges_nil` and `edges_cons` equations hold by `rfl`; the `edges_eq` theorem has the same statement, with only its induction proof referencing the explicit cons equation. No blanket noncomputable change, axiom, generated-name filtering, warning suppression or allowlist was introduced. One supporting proof, `StoredCandidates.original_edges_eq_fold`, changes only the simp argument `ExecutableVoting.edges` to `ExecutableVoting.edges_cons`; its theorem statement and all definitions in that file remain unchanged. The other 484 project closure sources are byte-identical to the accepted source.

`LegacyEquivalence.lean` imports the actual preserved old implementation from `.lake/controller-pilot/lib/lean`, defines the byte-identical replacement body, and proves pointwise equality by list induction. All 486 preserved old object hashes and the old source snapshot are verified before that proof. The successful strict comparison reports only `propext`, `Classical.choice` and `Quot.sound`. It is a new semantic comparison, not a fresh-project gate using historical objects.

`PilotCheck.lean` checks safe, total, computable metadata; explicit List.rec use; no self-reference; and absence of `ExecutableVoting.edges._unsafe_rec`. Both original equations are checked definitionally. Executable fixtures cover empty input, admission, rejection and a repeated edge. These checks pass without warnings and make no complexity claim.

## Validation method

Fresh project outputs use only `.lake/edges-pilot/lib/lean` plus pinned dependency caches and the official toolchain. There is no old project-object fallback. All 486 project modules are rebuilt sequentially with `lean -j1 -DautoImplicit=false -DwarningAsError=true`, including the aggregate. Dependencies are reused, not claimed freshly rebuilt.

The complete actual-owner audit and official target resolver are byte-identical to the accepted versions except for their output directory. All owners and recursive types/bodies, opaque values and recursor rules remain covered. The audit rejects unsafe/partial declarations and axioms outside `propext`, `Classical.choice`, `Quot.sound`, writing all diagnostics before failure. A remaining partial is not excused by successful kernel replay.

Before singleton replay, the official Lean resolver enumerates actual modules and objects using the pinned checker's selection semantics. The supervisor repeats a filesystem check under lock and rejects aggregate prefixes. `LEAN_SYSROOT` identifies the official toolchain to avoid a nested prefix query. Only the repaired leaf is replayed; no aggregate-prefix checker or parallel worker is started.

## Raw evidence and preserved attempts

UUID attempt directories retain submitted-source snapshots, raw logs, preflights, commands/options, PIDs, lock inode, UTC/monotonic times and exit/reaping status. Two initial comparison attempts failed: an invalid `List.rec_cons` identifier/proof rewrite and then an unused section-variable diagnostic. One production compilation failed because `votes_eq` simplified inside the recursor before the induction hypothesis could rewrite it. A downstream proof then exposed the old simplifier-unfolding dependency. An attempted `eqns` registration failed to preserve that behavior and was removed; the explicit cons theorem supports the one-token downstream proof repair. Both failed compilations are retained. Their raw diagnostics, including the failed proof's printed `sorryAx`, are preserved; they are not successful proof evidence. The successful final comparison and final source do not contain `sorryAx`.

`reconcile.py` checks all source/object/import hashes, command coverage, raw successful diagnostics, complete dependency closure, exact partial-set difference, singleton resolution, receipt/preflight bijection and non-overlap, and preservation of prior evidence. `audit-export/manifest.json` lists ordered row-aligned chunks and the reconstruction SHA256; concatenate listed bytes without extra separators or headers.

The official toolchain is Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. All nine pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. No default Lake build, runtime shim, website change or automatic CI is used. Publication is additive with `[skip ci]` and ends at independent review before another definition is touched.

## Environment continuity

A parent callback reported disconnection at 12:55 UTC. The persisted observation at 12:56:02 UTC found the existing sequential build and its recorded child PID active under the same universal lock inode, with 361 modules completed. Resources were approximately 21.6 GiB free disk and a 16 GiB memory limit. No duplicate invocation or recovery compiler was started; the existing runner continued. The raw process table, active receipt UUID/PID, `/proc` state, lock device/inode and resource values are retained in `evidence/disconnection-continuity-observation.json`.

## Final fresh results

All 486 project modules strictly compile with zero warning headers. There are 488 successful compile invocations because two intermediate objects were rebuilt after the equation-interface repair; final object/import/source hashes are reconciled separately. One official resolver-guarded singleton replay passes for `LightEFTSpanners.ExecutableVoting`, with exactly one replay line. No aggregate-prefix checker was invoked.

The fresh complete audit inventories **9,310 actual-owner roots, 60,729 recursively visited constants and 48 opaque bodies**. It removes exactly `LightEFTSpanners.ExecutableVoting.edges._unsafe_rec`, introduces no partial, and retains the other **55** partial roots unchanged. There are zero unsafe project roots and zero aggregate-owned declarations. The strict audit exits 1 with **110 findings**: one root and one recursive finding per remaining partial. This is not a passing strict gate, and no CI is started.

The owner-name delta removes nine old generated declarations and adds the two explicit equation lemmas, all within ExecutableVoting. This explains the net reduction of seven roots; no name was filtered. The full delta and remaining names are exported.

All **501** new UUID receipts have matching persisted preflights and verified source snapshots. Intervals do not overlap, the universal lock inode is constant, and every child was reaped. Six nonzero attempts remain: the five development failures described above and the final expected strict-audit rejection. Three semantic-comparison invocations succeeded during development; the final one binds the final production source. Two successful executable/metadata checks are retained. Successful strict compilation has no warning headers; raw failed diagnostics and hints remain intact.

The 208 ordered audit chunks reconstruct the original TSV. All 2,725 accepted Controller evidence entries and all 5,161 earlier strict-aggregate entries were rehashed unchanged. The historical 494-preflight/495-receipt qualification remains explicit and is not replaced by the new 501/501 record. Paused for independent review before any other definition is repaired.
