# Light EFT graph entries 372–486: Stopped at the first failure

Frozen source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. Base evidence: `be04b7f6a38a951cf41d6da43e871c58e3063fe2`. Actual result: **137 passing stages, 45 complete new ordinary chains, 1 guard-rejected replay, 205 unattempted stages** out of 114 ordinary modules plus one compile-only aggregate / 343 planned stages. New results await independent review; whole-paper acceptance is not claimed.

**45 ordinary chains completed, 137 stages passed, and stage 138 was rejected by the unchanged whole-process supervision guard.** `CorePartitionBudget` (entry 417) compilation and exact resolution passed, but its singleton replay is **not accepted**, despite printing `replaying LightEFTSpanners.CorePartitionBudget` and the final owned wait4 reporting exit 0. Those are preserved observations, not a substitute for the required successful supervision result. The last complete ordinary module was `CoreGraphWeight` (entry 416). All new results await independent review; prior 371-chain acceptance is preserved.

At **2026-10-18T01:51:36.389427+00:00**, the snapshot contained a still-live thread **TID 275245 / TGID 275244**, state R, with missing required RSS/VM values. The owned waitid probes had not confirmed terminal completion, and the group did not meet the identity-checked live shared-mm or bounded exiting-only criteria. The supervisor sent SIGKILL to the owned group; **the final wait4 exit was nevertheless 0**, so no causal claim is made that the signal killed the checker. The stage remains failed because the telemetry/supervision contract was not satisfied. No lifecycle repair, retry, cap change or whitelist expansion was performed. [supervision-stop.json](supervision-stop.json), the [failed receipt](attempts/138-LightEFTSpanners.CorePartitionBudget-replay/receipt.json), [raw singleton output](attempts/138-LightEFTSpanners.CorePartitionBudget-replay/raw.log), complete samples and controller traceback preserve the diagnostics.

This was **not a recorded headroom-floor breach**: admission/preexec visible headroom was 4,606,660,608 / 4,602,183,680 bytes; the stop sample had 4,493,512,704 visible bytes and host MemAvailable 17,507,442,688 bytes. The failed replay is a supervision rejection, not a recorded kernel proof rejection. All children were reaped and the common lock released after final preservation.

**46 ordinary compilations and 46 exact resolutions passed; 45 singleton replays passed supervision.** The guarded replay was the 46th replay attempt and is excluded from successful replay/chain counts. **205 stages were not attempted**, including the sole aggregate compilation. No aggregate compile, resolver, prefix replay or `--fresh` substitution ran. The root retains **417 objects / 346 resolutions**, including the pending `CorePartitionBudget` compile/resolution; all original 371 objects and 300 resolutions are unchanged.

## Accepted scope and sequencing

Independent review accepts all 27 new chains at `be04b7f6a38a951cf41d6da43e871c58e3063fe2`, bringing the prior total to 371. All 81 receipts/logs, 27 resolutions, retained-object bindings, 210 text hashes, preservation and reaping passed. This records source/log/hash review, not fresh execution. The 371 accepted objects and 300 resolutions were verified against exact content/identity and root file/directory membership, then reused without accepted-stage reruns.

Ordinary chains are exactly frozen graph entries **372–485**, from `LightEFTSpanners.StoredOriginalCandidateRecords` through `LightEFTSpanners.NativeSquareRootOutput`. Entry 486 `LightEFTSpanners` is compilation only; resolver and prefix replay are forbidden. All **171 ordinary project-import edges** resolve to accepted seeds or earlier entries. [PLAN.json](PLAN.json) and [preparation-checks.json](preparation-checks.json) bind this scope; [module-status.json](module-status.json) gives each actual stage, UUID, receipt, source/object hash, and whether the chain completed. No other paper was compiled.

Actual access, resources, worker exclusion and the common lock were checked before launching once; see [launch-preflight.json](launch-preflight.json). Saved state and the exclusive invocation claim prevent duplicate execution. Any interruption reconciliation is preserved alongside the evidence. No unrelated SCC evidence is used.

## Commands, controls, and raw diagnostics

Official unmodified **Lean 4.34.0** was used, with all nine dependency revisions unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Lean executable SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; checker SHA256 is `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`. [source-toolchain-object-hashes.json](source-toolchain-object-hashes.json) records all prepared source hashes, actual retained objects, tools, and pins; executed stages are enumerated separately.

Ordinary stages use compile → exact resolver → singleton official replay, sequentially. The aggregate has only a compile stage, explicitly classified `aggregate_compile` while the child supervisor retains its unchanged compile execution path. Aggregate resolver/replay are rejected by the stage matrix and command guard; the existing resolver source also retains its aggregate refusal. No aggregate prefix replay or `--fresh` substitution is allowed or performed. Compile/resolver flags are `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`. Compilers use `MIMALLOC_ARENA_RESERVE=128MiB` and logs confirm `arena_reserve: 131072 KiB`. Replays use `leanchecker -v MODULE`, with `LEAN_NUM_THREADS=1` and `LEAN_STACK_SIZE_KB=65536`; each passing replay's output is checked as exactly its singleton. [result-reconciliation.json](result-reconciliation.json) includes full argv/environment and outcomes for every attempted stage. Receipts retain exact submitted-source snapshots/hashes; raw.log and samples.jsonl remain verbatim with their receipt-bound hashes.

Ordinary admission gates remained **3 GiB for compile/resolve and 4 GiB for replay**, including the first compile and the aggregate compile. The historical 4.375 GiB first-stage exception is removed completely; no first-stage exception applies. Historical 5 GiB wording in the unchanged advice-helper docstring does not set policy. Actual gate code and receipts determine admission. AS 12 GiB, CPU 60 s, wall 90 s, FSIZE 16 MiB, CORE 0, sampled RSS stop 6 GiB, per-cgroup anonymous-growth stop 3 GiB, runtime visible/host floor 1 GiB, host admission 3 GiB, and 100 ms sampling remain unchanged. The reviewed child runner, telemetry, limit readback, ownership, teardown grace, cleanup, and lease helpers are byte-identical to accepted controls. No lifecycle redesign, diagnostic pilot, or repeated fixture suite was run. Maximum sampled RSS was **3524935680 bytes**; sampled peaks are not continuous maxima. Null teardown metrics remain preserved and do not alone establish terminal completion.

Anchored Lean warning headers: **0**. Mimalloc verbose option/statistic lines are allocator diagnostics, not Lean warnings; hints are not counted as additional warning headers. Failed attempts and partial outputs are preserved, not relabeled or retried. Failure detail:

```json
{
  "module": "LightEFTSpanners.CorePartitionBudget",
  "graph_entry": 417,
  "stage_number": 138,
  "attempt_id": "0fd875cd7cf646acbb0b8453db16a991",
  "receipt": "attempts/138-LightEFTSpanners.CorePartitionBudget-replay/receipt.json",
  "stop_sample_utc": "2026-10-18T01:51:36.389427+00:00",
  "stop_decision_errors": [
    "{'operation': 'whole-process supervision', 'error': 'Missing memory telemetry for still-live TID 275245'}",
    "{'operation': 'whole-process supervision', 'error': 'No identity-checked live shared-mm telemetry or bounded exiting-only group'}"
  ],
  "still_live_tid": {
    "tid": 275245,
    "tgid": 275244,
    "start_ticks": 18822055,
    "state": "R",
    "rss": null,
    "vm": null,
    "stat_vsize_bytes": 1590644736,
    "stat_rss_pages": 28015,
    "collection_errors": [
      {
        "operation": "VmRSS",
        "error": "Missing required live value"
      },
      {
        "operation": "VmSize",
        "error": "Missing required live value"
      }
    ]
  },
  "observed_wait4_exit": 0,
  "stage_accepted": false,
  "direct_child_reaped": true,
  "all_descendants_gone": true,
  "aggregate_compiled": false
}
```

## Exact finite advice scope

No whitelist expansion was authorized or performed in this batch. The finalized-data scope remains exactly **2,905 files / 1,204,978,029 bytes**, with the same six accepted manifest authorities, TOP-plus-attempt-data selector and all exact byte/hash/count, per-manifest, regular/non-executable, no-symlink, same-descriptor identity/content and duplicate checks. The original selection and same-FD initial preservation handling remain byte-identical to the preceding reviewed controls. Ordinary verified handling may reuse these exact finalized-data bindings when actual capacity requires it. No new source/code, object-payload, executable/library or unlisted advice target is added.

The unchanged previously approved archive/data scope was renewed exactly once before the first planned stage, **2026-10-18T01:18:11.695811+00:00–2026-10-18T01:18:13.972275+00:00**, without expansion: scope A 3,809 archive files / 818,684,031 bytes; scope B 708 selected finalized data files / 385,582,329 bytes; combined **4,517 files / 1,204,266,360 bytes**. Authorities and selection remain the accepted ones. The pass hashes each approved new file and advises the same verified descriptor; [one-time-extension-verified.jsonl](one-time-extension-verified.jsonl) retains all bindings. [one-time-cache-advice.json](one-time-cache-advice.json) retains fresh actual before/after capacity. The 89 subsequent ordinary advice passes exclude those archive/data scopes, retaining only the existing legacy/finalized bindings. The reviewed bootstrap and initial finalized-data handling also retain their original exact scopes.

No deletion, extraction, cache installation, global cache drop, whitelist expansion, repeated archive/data pass or inferred reclaimed-byte credit occurred. Recorded agreement with local candidate archive hashes establishes no stronger dependency-installation provenance. Earlier failures and historical cache qualifications remain in prior checkpoints.

## Aggregate compilation accounting

`LightEFTSpanners` at entry 486 is import-only: **429 unique imports, no declarations**, all closed against accepted objects or preceding ordinary entries. The 114 ordinary modules have 171 direct project-import edges. All 115 source files match frozen Git bytes and hashes. Aggregate source SHA256 is `559f4d8d4eb86a4bee7701c29c47b2f2e218fff9264f9d70e8d2a89116fb6eac`. The existing resolver source SHA256 `9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf` is unchanged, including the explicit aggregate-target refusal. The aggregate's object is stored as `objects/LightEFTSpanners.olean`; it is not a namespace-prefix replay target. No aggregate resolution file may be created.

| Kind | Passing compiles | Exact resolutions | Singleton replays | Complete ordinary chains |
| --- | ---: | ---: | ---: | ---: |
| New ordinary modules | 46 | 46 | 45 | 45 |
| Aggregate | 0 | 0 | 0 | 0 |

A fully successful result contains **486 retained objects**, **485 cumulative ordinary chains after independent review**, and **414 resolutions**. Only 115 of those objects are new in this batch; 371 accepted objects were reused. The aggregate is always reported separately as compilation, never as a replay chain. Actual counts below and in [result-reconciliation.json](result-reconciliation.json) govern any partial outcome. Final exhaustive owner/axiom audit, dependency provenance and whole-paper acceptance remain separate.

## Full preservation and retained outputs

One canonical initial/final pair under one continuous universal lease checked **82755 bindings**, with all paths attempted, no changes, and matching digest `3c94b2d2f5078a8ea3d9557c3ed2cc1dbcbe0a731b7bae30f91cddfa5e63befb`. Initial completion: **2026-10-18T01:18:02.922306+00:00**. Final completion: **2026-10-18T01:52:06.688118+00:00**. [inputs.jsonl](inputs.jsonl), [final-content-verification.json](final-content-verification.json), and [reconciliation.log](reconciliation.log) preserve the evidence. Intermediate checks use the existing compact identities, membership checks and small source/control hashes. No additional full input-body pass was performed for publication.

The unchanged retained root is `.lake/light-eft-batch100-entries72-171-20261017-ee496fe7834c4e86994b3933112caff7`. It now contains **417 ledger objects and 346 successful resolution files**, with all original 371 objects and 300 resolutions unchanged. Any additional failed partial paths are listed in reconciliation. All retained object payloads and resolutions are copied into this checkpoint; [retained-root-binding.json](retained-root-binding.json) binds the original membership, while [output-records.jsonl](output-records.jsonl) records append-only output progress.

Supervisor PID **264113**, FD **3**, device **33**, inode **3849** held the universal lease from **2026-10-18T01:17:26.507161+00:00** through **2026-10-18T01:52:10.459839+00:00**. UUIDs and PIDs are unique, receipt intervals do not overlap, and all children were reaped. Final verification preceded verified kernel ECHILD and lock release. Batch end: **2026-10-18T01:52:10.459977+00:00**. See [batch-lock.json](batch-lock.json) and [batch-result.json](batch-result.json).

## Publication and remaining qualifications

The evidence is published additively on `light-eft-spanners-checkpoints`, with both commits marked `[skip ci]`. [PUBLICATION.json](PUBLICATION.json) binds the result commit; [evidence-sha256.json](evidence-sha256.json) lists every checkpoint file except itself and bytecode. Raw formatting is preserved; [publication-checks.json](publication-checks.json) retains full whitespace diagnostics and the scoped check. Read-only reconciliation command: `python3 -B checkpoints/light-eft-batch343-with-aggregate-20261018/verify_publication.py`; it runs no Lean, advice, fixtures, or full frozen-input pass.

No automatic CI, default Lake build, dependency update, shim, accepted-stage rerun, source edit, website edit, or change to old evidence occurred. No new exhaustive owner/axiom audit, coordinated clean/full CI, or mathematical acceptance was performed. Visible accounting remains **PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN**. Mathematical hypotheses and historical provenance/final-audit/paper qualifications remain unchanged. This is an incremental finite batch; new chains await independent review and no whole-paper completion is claimed. [terminal-environment.json](terminal-environment.json) records current resources and the idle compiler/free-lock state. Paused for independent review.
