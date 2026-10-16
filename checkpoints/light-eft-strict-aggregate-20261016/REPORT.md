# LightEFT strict aggregate and exact-source gate

Status: **486 strict compilations and 485 leaf/support singleton replays passed; the complete all-owner diagnostic export is available, but the strict all-owner no-partial audit gate failed. No clean CI was triggered.** Independent review is required. Theorem 34 remains open; runtime and whole-paper completion are excluded. Tested source: `e9d3f5ca8fe07062976d1681f8ad24294df6bb10`. Exact source and evidence binding is recorded in `evidence/source-binding.json` and the publication handoff.

## Scope and preserved review

This continues LightEFT source/docs `0c3d4c62ecf5f74c85b6589a0300c999945b8688` and evidence `85fe8c209ac442bb6729e168c8c00dc870143101`, on `light-eft-spanners-checkpoints`. The accepted native residual/square-root source is `753ae06c2921597cb39cd72bde25bc99e13a71e5`, with evidence `88fa6ea4990488c2d3af870283ba47d6b35fec85`. Prior acceptance is recorded as source/log/hash reconciliation, not fresh reviewer execution or CI. All 95 prior blocked-checkpoint entries and 122 accepted residual-checkpoint entries were rehashed successfully.

The source-derived closure is 429 LightEFT leaves, 56 necessary LightSpanners support leaves and the LightEFT aggregate: 486 modules. Every LightEFT leaf occurs in the closure. No default Lake build, other-paper target, website change, dependency update, runtime shim or parallel worker is used. The seven LightSpanners source edits below are required imports of this LightEFT aggregate, not a separate paper task.

## Mechanical repairs

The parent explicitly authorized minimal semantics-preserving inherited-linter repairs while retaining `warningAsError` and all mathematical assumptions. The original `TreePruning` failure and its submitted source remain unchanged in the prior checkpoint. The repair renames `hKG` to `_hKG`; its proposition remains an argument.

Seventeen proof files have mechanical edits, listed in `evidence/mechanically-modified-files.json`; `evidence/mechanical-source-diff.patch` records the exact diff. The other 469 module sources are unchanged. Repairs consist of unused binder renames, removal of unused simp arguments, deprecated lemma replacements, equivalent `simp`/`simpa` and tactic sequencing, removal of dead tactics, proof-local `haveI`/`letI` changed to `have`/`let`, and explicitly retaining automatically included unused instance parameters. For the latter, `omit ... in` removes automatic inclusion and the same instance parameter is immediately reintroduced explicitly in the theorem declaration. No mathematical assumption is deleted and no linter is suppressed.

Ten modified LightEFT files: TreePruning, HostCounting, Blocking, GraphPruning, BipartiteForcing, BlowupCertificateObstruction, FaultBudgetSaturation, HubPreserver, CounterfamilyWeight, GenericBlowupFailure. Seven required support files: PaddingPositions, BucketRestriction, RetainedGraph, EndpointSampling, SamplingCounting, LightnessBound, MainTheorem.

Fourteen failed strict compilation attempts are preserved in UUID directories. Thirteen expose inherited linters promoted to errors; one is the repair's misplaced `omit` after a doc comment, corrected by placing it before the comment. These are not paper counterexamples or mathematical/kernel failures. Warning headers are counted by anchored Lean diagnostic headers, not occurrences of the word in options or hints; strict diagnostics here are errors, not warnings. No inherited-diagnostic baseline workaround is used.

## Local validation

The unmodified official Lean 4.34.0 toolchain and all nine pinned dependencies are retained. The official Lean commit is `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; mathlib is `5ed2965256430c3649e86755f9576b54eca72435`; manifest SHA256 is `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f`. Local dependency objects are reused incrementally; this is not a clean local dependency rebuild.

Entry points, each strictly sequential:

```
python checkpoints/light-eft-strict-aggregate-20261016/run.py build
python checkpoints/light-eft-strict-aggregate-20261016/run.py replay
python checkpoints/light-eft-strict-aggregate-20261016/run.py audit
```

Every project compile uses official `lean -j1 -DautoImplicit=false -DwarningAsError=true --root=SOURCE_ROOT -o OBJECT SOURCE`. Every successful leaf/support kernel replay uses official `leanchecker -v MODULE`, requiring the exact singleton output `replaying MODULE`. There are 485 such modules; the import-only aggregate is compiled and has zero owned declarations. The failed extra aggregate-prefix invocation and its sequencing qualification are detailed below. The audit uses official Lean with `-j1 -DautoImplicit=false -DwarningAsError=true`. Authoritative argument arrays are in `evidence/commands.jsonl` and each UUID receipt; paths with spaces are separate arguments, not shell command fragments.

The audit inventories declarations by actual defining-module owner across the entire LightEFT and required LightSpanners closure, including declarations outside the expected namespaces. It recursively visits every root's type and body, opaque bodies, mutual inductive families, constructors and recursor-rule right-hand sides; it rejects unsafe/partial declarations and every axiom except `propext`, `Classical.choice`, `Quot.sound`. It does not rely on cached collectAxioms results. Every expected leaf import must be loaded. The first strict audit stopped at `LightEFTSpanners.Controller.run._unsafe_rec`, which is marked partial. A second diagnostic-only audit retained every declaration, traversed the complete closure, wrote all findings, and deliberately returned failure under the same no-partial gate. No finding was suppressed or allowlisted.

All external compiler/checker invocations use `/tmp/distance-sparsification-single-compiler.lock`, unique UUID source-bound receipts, submitted source snapshots/SHA256, PID, UTC/monotonic timing, and child reaping. Raw logs, failed snapshots and chronological attempts are retained. The hash-aware build runner only reuses a successful strict compile if its source, imported project objects and own object hashes all match. Final reconciliation checks all 486 source/object/import sets and all 485 singleton replays. The erroneous aggregate-prefix invocation had parallel internal checker tasks despite one external process; this historical qualification is retained, not hidden by the non-overlapping external receipts.

## Clean CI preparation

`scripts/LightEFTExactCI.py`, `scripts/LightEFTSequential.py` and `scripts/LightEFTFullAudit.lean` define the dedicated clean gate. `.github/workflows/light-eft-exact.yml` is prepared separately from the multi-paper workflow; that workflow ignores pushes to this checkpoint branch. The gate uses an immutable exact source checkout, hash-pinned official Lean archive, all nine exact package revisions, the unmodified official cache CLI, 486 strict compilations, 485 leaf/support singleton replays and the full recursive audit. The aggregate prefix is explicitly excluded from replay because it owns no declarations and the official checker expands prefixes into parallel tasks. Cache CLI dependencies are bootstrapped sequentially with official Lean rather than Lake's parallel scheduler. Official cache settings are unchanged.

The workflow has one job, the repository-wide compiler concurrency group, and a public read-only active-run preflight. Local compiler/checker activity must stop before the normal push trigger. No API write bypass, credential addition or security change is used. UUID logs, snapshots, source/object/toolchain hashes, audit TSV and ordered chunks are uploaded even on failure. The workflow remains manual-only preparation and is not ready to claim a passing gate: its strict audit still rejects the generated partial companions. No trigger commit, CI run or CI artifact exists for this checkpoint. Source/evidence publication uses `[skip ci]`. The cache bootstrap smoke script is preserved as an unexecuted preparation; official cache retrieval was not newly exercised here.

## Mathematical boundary

See `Light Edge Fault Tolerant Graph Spanners/PROOF_COVERAGE.md`. The accepted native finite original-ID nonnegative-weight results retain their positive-parameter hypotheses, seed baseline, pruning loss and corrected stretch+1 extremal argument. Fixed-parameter lower-family uniformity qualifications, the printed-threshold correction and certificate counterexamples are unchanged. Theorem 34 is a substantive open obligation; efficient/native randomized runtime and whole-paper completion are not claimed.


## Complete diagnostic findings and blocker

The diagnostic inventory contains **9,327 actual-owner project declarations**. Full recursive type/body traversal covers **60,746 constants and 48 opaque bodies**, including mutual inductive families and recursor-rule right-hand sides. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

There are **57 distinct partial project declarations and zero unsafe project declarations**. Every partial name ends in `._unsafe_rec`. They produce 114 strict findings because each is listed at both root and recursive-dependency stages; 114 is not a count of distinct declarations. The complete inventory is retained, not filtered. `diagnostic-partial-roots.json` lists every one.

A read-only graph analysis of the exported dependencies starts from all 9,270 safe project roots. Its closure has 60,689 constants, no partial/unsafe dependencies and the same three axioms. `diagnostic-classification.json` records this bounded distinction. It does **not** turn the strict all-owner gate into a pass or certify runtime behavior.

The official Lean sources explain the pattern: `Lean/Elab/PreDefinition/Basic.lean` defines `addAndCompilePartialRec`, generating `DefinitionSafety.partial` implementations named through `Compiler.mkUnsafeRecName`; structural recursion invokes that path. The original `Controller.run` is an ordinary structurally recursive definition. `Lean/Replay.lean` explicitly skips partial and unsafe constants when selecting replay roots. Thus successful official singleton replays must not be described as replaying these implementation companions. Relevant official source snapshots and hashes are preserved under `evidence/official-toolchain-sources/`.

**Remaining gate obligation:** independently review how complete actual-owner inventory and generated runtime companions should be treated while retaining the strict safe-root dependency audit. No blanket partial-name allowlist, warning suppression, source rewrite, or baseline workaround was introduced. The existing strict gate remains failed, so a knowingly failing clean CI was not started.

## Failed aggregate-prefix attempt and continuity

After all 485 singleton leaf/support replays succeeded, an erroneous extra command `leanchecker -v LightEFTSpanners` was attempted (UUID `8f087e81bcc44504b44576a08cfc0b4a`). Inspection of the unmodified official `LeanChecker.lean` shows that non-fresh targets select module prefixes and launch `IO.asTask` for every match. The aggregate name therefore expanded into many internal replay tasks. This attempt was not singleton/sequential internally and is explicitly excluded from the successful replay claim. No parallel worker or second external compiler/checker was created by the supervisor.

The checker reached the 16 GiB cgroup limit and was OOM-killed, exit -9; the supervisor reaped it. An attempted controlled stop found the process already gone and sent no signal. The cgroup reported one OOM kill. Raw log (empty before failure), receipt, submitted aggregate source, memory observations and official checker source are retained. Future prepared CI performs only the 485 exact leaf/support replays. Aggregate compilation and the full owner audit cover the aggregate; the inventory proves it owns zero declarations.

The 11:25 UTC disconnection callback did not interrupt the running environment. At 11:26:32 UTC, a live check found 486 successful compilations and 477 completed replays, exactly one checker whose PID matched its receipt, and the common lock held. Source snapshots and completed-child reaping verified. The existing session continued without restart or duplicated work; see `continuity-1125-callback.json`. The later aggregate OOM is separately recorded and is not retroactively attributed to that callback.

## Evidence and terminal state

There are **988 unique source-bound external invocation receipts**: 486 successful strict compilations, 14 failed linter/repair compilations, 485 successful singleton replays, one failed aggregate-prefix replay, one failed initial strict audit and one deliberately failing complete diagnostic audit. All completed children were reaped; external invocation intervals do not overlap and share one lock inode. The internal-task exception is the failed aggregate-prefix attempt above. Every submitted snapshot hash is reconciled, including failed sources.

The diagnostic TSV is  preserved in full and in **208 ordered row-aligned chunks**. `audit-export/manifest.json` provides part hashes, byte counts and the reconstruction SHA256. Concatenate listed bytes without extra separators or headers. `reconcile.py` performs read-only source/object/log/hash checks and reconstructs these exports; it does not run Lean. `reconcile_ci_artifact.py` is preparation for a future passing clean gate and has not been exercised on a new CI artifact.

The terminal environment check is saved separately. Local compiler/checker activity is stopped before publication. No automatic CI is triggered. Prior source/evidence, raw failures, partial gate scripts and all mathematical qualifications remain preserved.
