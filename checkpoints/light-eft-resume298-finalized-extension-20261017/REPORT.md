# Light EFT graph entries 272–371: Stopped at the first failure

Frozen source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. Base evidence: `01cc49a0aa4994fec95a91fffcb3d1e1d83c04d7`. Actual result: **217 passing stages, 73 complete new chains, 1 guard-stopped compilation, 80 unattempted stages** out of 100 modules / 298 planned stages. New results await independent review; whole-paper acceptance is not claimed.

The first previously blocked `SeededSubtreePacking` replay passed without rerunning its accepted compile/resolution. Actual first-checker admission/preexec headroom was **4,504,432,640 / 4,499,963,904 bytes**, both above the unchanged **4,294,967,296-byte** gate. The exact authorized finalized-data extension and first-planned-stage housekeeping therefore ran successfully; this does not claim nominal advised bytes as admission credit.

The later first failure was **`LogarithmicVotingSamples` compilation, graph entry 345, stage 218**. Its admission/preexec headroom was **4,424,441,856 / 4,420,075,520 bytes**, above the ordinary 3 GiB gate. At **2026-10-18T00:32:28.580165+00:00**, visible headroom fell to **1,071,214,592 bytes**, **2,527,232 bytes below** the unchanged 1 GiB runtime floor. The worker sent group SIGKILL and reaped the child (exit -9); recorded OOM counters did not change. This is a recorded runtime resource-guard stop, not a compiler proof diagnostic or kernel rejection. No object was produced for the failed module, and there was no retry, cap change, or further whitelist expansion. See [runtime-stop.json](runtime-stop.json), the [failed receipt](attempts/218-LightEFTSpanners.LogarithmicVotingSamples-compile/receipt.json), and [invocation.log](invocation.log).

**72 compilations, 72 exact resolutions and 73 singleton replays passed** in this continuation. Together with the two previously accepted `SeededSubtreePacking` stages, these complete 73 chains (entries 272–344, through `VotingQueryCount`) pending independent review. The prior 271 qualified chains retain their acceptance. The failed compile and **80 unattempted stages** remain incomplete. Entry 372 was not run.

## Accepted scope and sequencing

Independent review accepted `SeededSubtreePacking` compilation and exact resolution at `01cc49a0aa4994fec95a91fffcb3d1e1d83c04d7`. Its 166,360-byte object has SHA256 `d498a05da9d0e78ac5e2bcbbd67a4fd215c347ab3957510d5e8354b97b591d41`. The prior total remains 271 qualified chains plus that accepted partial. This records source/log/hash review, not fresh execution. All 272 objects and 201 resolutions were verified and reused unchanged. Accepted compilation/resolution stages were not rerun. The first current stage is its singleton replay; the remaining 99 modules use compile → resolver → replay, for 298 new stages.

This batch contains exactly frozen graph entries **272–371**, from `LightEFTSpanners.SeededSubtreePacking` through `LightEFTSpanners.StoredCandidateDrawLookup`. Entry 372 `StoredOriginalCandidateRecords` is excluded. All **130 project-import edges** resolve to accepted seeds or earlier entries. [PLAN.json](PLAN.json) and [preparation-checks.json](preparation-checks.json) bind this scope; [module-status.json](module-status.json) gives each actual stage, UUID, receipt, source/object hash, and whether the chain completed. No other paper was compiled.

Actual access, resources, worker exclusion and the common lock were verified before launching once; [launch-preflight.json](launch-preflight.json) preserves that check. Saved state and the exclusive invocation claim prevent duplicate execution. Any interruption reconciliation is preserved with the evidence. No unrelated SCC evidence is used.

## Commands, controls, and raw diagnostics

Official unmodified **Lean 4.34.0** was used, with all nine dependency revisions unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Lean executable SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; checker SHA256 is `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`. [source-toolchain-object-hashes.json](source-toolchain-object-hashes.json) records all tested source, object, tool, and pin bindings.

The first planned stage is `SeededSubtreePacking` replay only; its accepted compile/resolution are reused. Thereafter the planned order is compile → exact resolver → singleton replay for each of the other 99 modules, sequentially. No accepted stage is rerun. Compile/resolver flags are `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`. Compilers use `MIMALLOC_ARENA_RESERVE=128MiB` and logs confirm `arena_reserve: 131072 KiB`. Replays use `leanchecker -v MODULE`, with `LEAN_NUM_THREADS=1` and `LEAN_STACK_SIZE_KB=65536`; each passing replay's output is checked as exactly its singleton. [result-reconciliation.json](result-reconciliation.json) includes full argv/environment and outcomes for every attempted stage. Receipts retain exact submitted-source snapshots/hashes; raw.log and samples.jsonl remain verbatim with their receipt-bound hashes.

Ordinary admission gates remained **3 GiB for compile/resolve and 4 GiB for replay**, including all compiles; the first planned checker requires 4 GiB. The historical Bernoulli 4.5 GiB exception is not used. The first checker uses the ordinary 4 GiB gate; the one-time housekeeping trigger is now this first planned stage, not a later compilation. Historical 5 GiB wording in the unchanged archive/data helper docstring is not policy; the actual gate function and receipts determine admission. AS 12 GiB, CPU 60 s, wall 90 s, FSIZE 16 MiB, CORE 0, sampled RSS stop 6 GiB, per-cgroup anonymous-growth stop 3 GiB, runtime visible/host floor 1 GiB, host admission 3 GiB, and 100 ms sampling remain unchanged. The reviewed child runner, telemetry, limit readback, ownership, teardown grace, cleanup, and lease helpers are byte-identical to accepted controls. No lifecycle redesign, diagnostic pilot, or repeated fixture suite was run. Maximum sampled RSS was **3446648832 bytes**; sampled peaks are not continuous maxima. Null teardown metrics remain preserved and do not alone establish terminal completion.

Anchored Lean warning headers: **0**. Mimalloc verbose option/statistic lines are allocator diagnostics, not Lean warnings; hints are not counted as additional warning headers. Failed attempts and partial outputs are preserved, not relabeled or retried. Failure detail:

```json
{
  "module": "LightEFTSpanners.LogarithmicVotingSamples",
  "graph_entry": 345,
  "attempt_id": "943d9c18f0814ecb80a945a1d7b8e574",
  "receipt": "attempts/218-LightEFTSpanners.LogarithmicVotingSamples-compile/receipt.json",
  "stop_sample_utc": "2026-10-18T00:32:28.580165+00:00",
  "stop_visible_bytes": 1071214592,
  "runtime_visible_floor_bytes": 1073741824,
  "shortfall_bytes": 2527232,
  "exit": -9,
  "worker_sent_group_SIGKILL": true,
  "failed_object_produced": false
}
```

## Exact finite advice scope

The only whitelist extension comprises two exact finalized-data subsets selected by the existing strict `finalized_scope.py` TOP/attempt selector: 700 files / 302,546,603 bytes from `light-eft-resume231-headroom45g-20261017/evidence-sha256.json` at `5394bf2db26dba05df53bb446b39e3609e7e03d9` (208,970 bytes, SHA256 `dff18c1ff38bdd5ae4d72daf442de7e6e65d9f9d88f4c57d2ed7d9c82b0b921c`), and 907 files / 323,761,596 bytes from `light-eft-batch100-entries172-271-20261017/evidence-sha256.json` at `7c5688da20649e4825015886b6b75536fe2b83e4` (291,668 bytes, SHA256 `31dd6035c63ba504519f47b54b72d388f2dc41b7e9e8260bbff9dd385487ee93`). Together they add exactly **1,607 files / 626,308,199 bytes**. Combined with the original 623 files, `reviewed_finalized_batch_data` is exactly **2,230 files / 860,349,332 bytes**. No wider search, object payloads, submitted source, executable/library files, or unlisted paths were added. Manifest byte/hash pins, per-authority subset budgets, duplicate/path exclusions and all same-descriptor content/identity/mode checks are retained. The updated assertions consistently require these exact combined totals.

The combined finalized-data subset is hashed and advised through the existing same-FD initial-preservation path. The separate archive/data pass is triggered exactly once by the first planned checker, with an exclusive claim file, never by recompiling an accepted object. Fresh measured admission and preexec headroom must both meet 4 GiB; nominal advised bytes are never admission credit. Subsequent ordinary legacy-only handling may reuse the verified finalized-data bindings under the existing capacity policy. Controller diffs and the exact remaining-stage matrix are in [preparation-checks.json](preparation-checks.json). No lifecycle or resource-bound code changed.

The unchanged, previously reviewed archive/data scope was renewed exactly once before the first planned checker, **2026-10-17T23:39:32.358714+00:00–2026-10-17T23:39:34.576540+00:00**, without expansion: scope A 3,809 archive files / 818,684,031 bytes; scope B 708 selected finalized data files / 385,582,329 bytes; combined **4,517 files / 1,204,266,360 bytes**. Authorities and selection remain the accepted ones. The pass hashes each approved new file and advises the same verified descriptor; [one-time-extension-verified.jsonl](one-time-extension-verified.jsonl) retains all bindings. [one-time-cache-advice.json](one-time-cache-advice.json) retains fresh actual before/after capacity. The 144 subsequent ordinary advice passes exclude those archive/data scopes, while retaining the authorized finalized-data subset. The reviewed bootstrap and initial finalized-data handling also retain their original exact scopes.

No extraction, cache installation, global cache drop, additional whitelist expansion, repeated archive/data pass, or inferred reclaimed-byte credit occurred. Recorded agreement with local candidate archive hashes establishes no stronger dependency-installation provenance. The prior replay admission refusal at `01cc49a0aa4994fec95a91fffcb3d1e1d83c04d7` remains a refusal; it is not relabeled. This is a separately authorized finite continuation with the approved finalized-data extension. Historical cache qualifications remain unchanged.

## Full preservation and retained outputs

One canonical initial/final pair under one continuous universal lease checked **81870 bindings**, with all paths attempted, no changes, and matching digest `bc732b4dea825596472b08f4d2dfb28c1e0befa6b14ea07284ccf0cdce976cbd`. Initial completion: **2026-10-17T23:39:23.594362+00:00**. Final completion: **2026-10-18T00:33:00.704888+00:00**. [inputs.jsonl](inputs.jsonl), [final-content-verification.json](final-content-verification.json), and [reconciliation.log](reconciliation.log) preserve the evidence. Intermediate checks use the existing compact identities, membership checks and small source/control hashes. No additional full input-body pass was performed for publication.

The unchanged retained root is `.lake/light-eft-batch100-entries72-171-20261017-ee496fe7834c4e86994b3933112caff7`. It now contains **344 ledger objects and 273 successful resolution files**, with all original 272 objects and 201 resolutions unchanged. Any additional failed partial paths are listed in reconciliation. All retained object payloads and resolutions are copied into this checkpoint; [retained-root-binding.json](retained-root-binding.json) binds the original membership, while [output-records.jsonl](output-records.jsonl) records append-only output progress.

Supervisor PID **238062**, FD **3**, device **33**, inode **3849** held the universal lease from **2026-10-17T23:38:48.193000+00:00** through **2026-10-18T00:33:04.666336+00:00**. UUIDs and PIDs are unique, receipt intervals do not overlap, and all children were reaped. Final verification preceded verified kernel ECHILD and lock release. Batch end: **2026-10-18T00:33:04.666678+00:00**. See [batch-lock.json](batch-lock.json) and [batch-result.json](batch-result.json).

## Publication and remaining qualifications

The evidence is published additively on `light-eft-spanners-checkpoints`, with both commits marked `[skip ci]`. [PUBLICATION.json](PUBLICATION.json) binds the result commit; [evidence-sha256.json](evidence-sha256.json) lists every checkpoint file except itself and bytecode. Raw formatting is preserved; [publication-checks.json](publication-checks.json) retains full whitespace diagnostics and the scoped check. Read-only reconciliation command: `python3 -B checkpoints/light-eft-resume298-finalized-extension-20261017/verify_publication.py`; it runs no Lean, advice, fixtures, or full frozen-input pass.

No automatic CI, default Lake build, dependency update, shim, accepted-stage rerun, source edit, website edit, or change to old evidence occurred. No new exhaustive owner/axiom audit, coordinated clean/full CI, or mathematical acceptance was performed. Visible accounting remains **PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN**. Mathematical hypotheses and historical provenance/final-audit/paper qualifications remain unchanged. This is an incremental finite batch; new chains await independent review and no whole-paper completion is claimed. [terminal-environment.json](terminal-environment.json) records current resources and the idle compiler/free-lock state. Paused for independent review.
