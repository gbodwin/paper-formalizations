# Light EFT graph entries 272–371: Stopped at the first failure

Frozen source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. Base evidence: `7c5688da20649e4825015886b6b75536fe2b83e4`. Actual result: **2 passing stages, 0 complete new chains, 1 refused replay admission, 297 unattempted stages** out of 100 modules / 300 planned stages. New results await independent review; whole-paper acceptance is not claimed.

The genuine blocker was **visible checker-admission capacity**, not a failed proof or kernel rejection. At **2026-10-17T23:27:48.250741+00:00**, the ordinary 4 GiB gate required **4,294,967,296 bytes**, while fresh measured visible headroom was **3,980,185,600 bytes**, short by **314,781,696 bytes**. Host MemAvailable was **17,653,698,560 bytes**. The reviewed legacy-only advice pass had already completed; no additional advice, retry, or cap change followed. See [admission-refusal.json](admission-refusal.json) and the [failed source-bound receipt](attempts/003-LightEFTSpanners.SeededSubtreePacking-replay/receipt.json).

**No new chain completed.** `SeededSubtreePacking`'s compilation and exact resolution are preserved as partial results pending independent review; its object is not counted as a newly qualified chain. The other 99 modules were not executed. No later stage was attempted. The refused-admission directory has no child execution log or sample stream because no checker child started; its receipt and the full controller traceback in [invocation.log](invocation.log) preserve the failure.

## Accepted scope and sequencing

Independent review accepted all 300 stages at `7c5688da20649e4825015886b6b75536fe2b83e4`, bringing the prior total to 271 qualified chains. This is a record of source/log/hash review, not fresh execution. The 271 accepted objects and 200 resolutions were checked against their saved bindings and exact root file/directory membership, then reused without accepted-stage reruns.

This batch contains exactly frozen graph entries **272–371**, from `LightEFTSpanners.SeededSubtreePacking` through `LightEFTSpanners.StoredCandidateDrawLookup`. Entry 372 `StoredOriginalCandidateRecords` is excluded. All **130 project-import edges** resolve to accepted seeds or earlier entries. [PLAN.json](PLAN.json) and [preparation-checks.json](preparation-checks.json) bind this scope; [module-status.json](module-status.json) gives each actual stage, UUID, receipt, source/object hash, and whether the chain completed. No other paper was compiled.

Actual access, resources, worker exclusion, and the common lock were verified before launching once. The retained plan and invocation claim prevent duplicate execution; any later interruption reconciliation is preserved alongside the batch evidence. No unrelated SCC evidence is used.

## Commands, controls, and raw diagnostics

Official unmodified **Lean 4.34.0** was used, with all nine dependency revisions unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Lean executable SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; checker SHA256 is `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`. [source-toolchain-object-hashes.json](source-toolchain-object-hashes.json) records the 100 prepared source bindings, retained objects, tools, and pins; only the first module and resolver were executed.

The planned order was compile → exact resolver → singleton replay, sequentially. Only the first compilation and resolver executed. The first replay was refused at admission before any checker child or preexec handshake; no kernel replay ran in this batch. Compile/resolver flags are `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`. Compilers use `MIMALLOC_ARENA_RESERVE=128MiB` and logs confirm `arena_reserve: 131072 KiB`. Replays use `leanchecker -v MODULE`, with `LEAN_NUM_THREADS=1` and `LEAN_STACK_SIZE_KB=65536`; each passing replay's output is checked as exactly its singleton. [result-reconciliation.json](result-reconciliation.json) includes full argv/environment and outcomes for every attempted stage. Receipts retain exact submitted-source snapshots/hashes; raw.log and samples.jsonl remain verbatim with their receipt-bound hashes.

Ordinary admission gates remained **3 GiB for compile/resolve and 4 GiB for replay**, including the first compile. The historical Bernoulli 4.5 GiB exception is not used. Historical 5 GiB prose in the unchanged advice helper does not set admission policy; the ordinary gate function and actual receipts determine the gates. AS 12 GiB, CPU 60 s, wall 90 s, FSIZE 16 MiB, CORE 0, sampled RSS stop 6 GiB, per-cgroup anonymous-growth stop 3 GiB, runtime visible/host floor 1 GiB, host admission 3 GiB, and 100 ms sampling remain unchanged. The reviewed child runner, telemetry, limit readback, ownership, teardown grace, cleanup, and lease helpers are byte-identical to accepted controls. No lifecycle redesign, diagnostic pilot, or repeated fixture suite was run. Maximum sampled RSS was **2981777408 bytes**; sampled peaks are not continuous maxima. Null teardown metrics remain preserved and do not alone establish terminal completion.

Anchored Lean warning headers: **0**. Mimalloc verbose option/statistic lines are allocator diagnostics, not Lean warnings; hints are not counted as additional warning headers. Failed attempts and partial outputs are preserved, not relabeled or retried. Failure detail:

```json
{
  "attempt_id": "bbf92d26fb6a4ca596789b784a7d6fe2",
  "receipt": "attempts/003-LightEFTSpanners.SeededSubtreePacking-replay/receipt.json",
  "visible_admission_bytes": 3980185600,
  "required_visible_bytes": 4294967296,
  "shortfall_bytes": 314781696,
  "host_MemAvailable_bytes": 17653698560,
  "no_checker_child_spawned": true,
  "preexec_not_reached": true,
  "executed_Lean_children": 2,
  "executed_kernel_replays": 0,
  "unattempted_stages": 297,
  "completed_new_chains": 0
}
```

## Exact finite advice scope

The same reviewed finite new scope was renewed exactly once, **2026-10-17T23:27:16.592511+00:00–2026-10-17T23:27:18.838039+00:00**, without expansion: scope A 3,809 archive files / 818,684,031 bytes; scope B 708 selected finalized data files / 385,582,329 bytes; combined **4,517 files / 1,204,266,360 bytes**. Authorities and selection remain the accepted ones. The pass hashes each approved new file and advises the same verified descriptor; [one-time-extension-verified.jsonl](one-time-extension-verified.jsonl) retains all bindings. [one-time-cache-advice.json](one-time-cache-advice.json) retains fresh actual before/after capacity. The 2 subsequent ordinary advice passes exclude these new scopes. The reviewed bootstrap and initial finalized-data handling also retain their original exact scopes.

No extraction, cache installation, global cache drop, expansion, repeated new-scope advice, or inferred reclaimed-byte credit occurred. Recorded agreement with local candidate archive hashes establishes no stronger dependency-installation provenance. Earlier failures and historical cache qualifications remain in prior checkpoints.

## Full preservation and retained outputs

One canonical initial/final pair under one continuous universal lease checked **80255 bindings**, with all paths attempted, no changes, and matching digest `2f210695bbf0bd3295fc4d779d3b6b08f5fabe8feef7fbe55b93e87077b450d4`. Initial completion: **2026-10-17T23:27:08.287658+00:00**. Final completion: **2026-10-17T23:28:17.805611+00:00**. [inputs.jsonl](inputs.jsonl), [final-content-verification.json](final-content-verification.json), and [reconciliation.log](reconciliation.log) preserve the evidence. Intermediate checks use the existing compact identities, membership checks and small source/control hashes. No additional full input-body pass was performed for publication.

The unchanged retained root is `.lake/light-eft-batch100-entries72-171-20261017-ee496fe7834c4e86994b3933112caff7`. It now contains **272 ledger objects and 201 successful resolution files**, with all original 271 objects and 200 resolutions unchanged. Any additional failed partial paths are listed in reconciliation. All retained object payloads and resolutions are copied into this checkpoint; [retained-root-binding.json](retained-root-binding.json) binds the original membership, while [output-records.jsonl](output-records.jsonl) records append-only output progress.

Supervisor PID **236707**, FD **3**, device **33**, inode **3849** held the universal lease from **2026-10-17T23:26:32.190710+00:00** through **2026-10-17T23:28:21.655035+00:00**. UUIDs and PIDs are unique, receipt intervals do not overlap, and all children were reaped. Final verification preceded verified kernel ECHILD and lock release. Batch end: **2026-10-17T23:28:21.655177+00:00**. See [batch-lock.json](batch-lock.json) and [batch-result.json](batch-result.json).

## Publication and remaining qualifications

The evidence is published additively on `light-eft-spanners-checkpoints`, with both commits marked `[skip ci]`. [PUBLICATION.json](PUBLICATION.json) binds the result commit; [evidence-sha256.json](evidence-sha256.json) lists every checkpoint file except itself and bytecode. Raw formatting is preserved; [publication-checks.json](publication-checks.json) retains full whitespace diagnostics and the scoped check. Read-only reconciliation command: `python3 -B checkpoints/light-eft-batch100-entries272-371-20261017/verify_publication.py`; it runs no Lean, advice, fixtures, or full frozen-input pass.

No automatic CI, default Lake build, dependency update, shim, accepted-stage rerun, source edit, website edit, or change to old evidence occurred. No new exhaustive owner/axiom audit, coordinated clean/full CI, or mathematical acceptance was performed. Visible accounting remains **PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN**. Mathematical hypotheses and historical provenance/final-audit/paper qualifications remain unchanged. This is an incremental finite batch; the two successful stages await independent review, no new chain is accepted, and no whole-paper completion is claimed. [terminal-environment.json](terminal-environment.json) records current resources and the idle compiler/free-lock state. Paused for independent review.
