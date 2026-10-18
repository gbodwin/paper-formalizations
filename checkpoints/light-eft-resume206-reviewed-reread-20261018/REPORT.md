# Exact 206-stage Light EFT continuation — pending independent review

Frozen Lean source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
Prior production evidence: `95b0256dfdf05bf415248c764510701f1b7d5dfc`.
Approved supervisor repair: `7bec03140cb15d6fcd7fef6b3e9b71871acd404e`.

All **206 authorized production stages passed** in one finite sequential batch. The aggregate was compiled only. Mandatory final full preservation matched the initial inventory exactly. These are incremental validation results awaiting independent review; no whole-paper acceptance or completion is claimed.

## Review recorded and exact scope

The user reports independent acceptance of the repair's 445 manifest entries, 66 fixture receipts/leases, 44 final passing cases and 763 retained bindings. The approved `exit_transition.py` SHA256 is `1135140dd7dd3d075953d5d621f727a7a7c13796985c27da0c5afba68f95e76a`; approved `decision_telemetry.py` SHA256 is `08ae50f987ba67655e21d504e561ff5a23eda79104f35fe4c0d48e6e59de87fe`. Both implementations were reused byte-for-byte. This records the reported source/log/hash review; no fixtures were rerun in this continuation.

The batch starts with **416 independently qualified ordinary chains**, **417 retained objects** and **346 retained resolutions**. The CorePartitionBudget compilation and exact resolution were already accepted; its earlier replay remained rejected. No accepted stage was repeated.

| Scope | Compile | Resolve | Singleton kernel replay |
| --- | ---: | ---: | ---: |
| CorePartitionBudget, entry 417 | reused | reused | 1 |
| Entries 418–485, HubPreserver through NativeSquareRootOutput | 68 | 68 | 68 |
| Entry 486, LightEFTSpanners aggregate | 1 | forbidden | forbidden |
| New executed stages | **69** | **68** | **69** |

There are 69 newly completed ordinary chains pending review: the previously partial Core chain and 68 complete new chains. If independently accepted, the ordinary qualified total becomes **485**. The retained root now contains **486 objects** and **414 resolutions**. Aggregate compilation does not count as a replay-qualified ordinary chain. There was no automatic retry, stage expansion, default Lake build, extra compiler/checker invocation, new exhaustive owner/axiom audit, clean rebuild, or CI run.

## Commands, immutable inputs and execution ownership

The sole batch invocation was:

```text
python3 -B -u checkpoints/light-eft-resume206-reviewed-reread-20261018/run_batch.py
```

Its combined raw controller output is [invocation.log](invocation.log). Each numbered attempt directory retains the full structured argv/environment, UUID, submitted-source snapshot and SHA256, actual child PID/start identity, inherited lock handshake, limit readback, runtime decision samples, owned waitid/wait4 results, raw diagnostics, and output/resolution bindings. [result-reconciliation.json](result-reconciliation.json) indexes all 206 receipts in execution order. [PLAN.json](PLAN.json) fixes the allowed sequence; command construction refuses Core recompilation/resolution and aggregate resolution/replay.

Official Lean **4.34.0** was used with the existing nine pinned dependencies, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Compiler and resolver options remained `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`; compile commands add the exact source root and fresh `-o` object path. Replays used official `leanchecker -v <exact-module>`, with `LEAN_NUM_THREADS=1` and the existing stack setting. `MIMALLOC_ARENA_RESERVE=128MiB` was retained; every compilation's allocator diagnostic confirmed the expected 131072 KiB option. Exact executable, resolver, source graph, individual source, harness, object and resolution hashes are in [source-toolchain-object-hashes.json](source-toolchain-object-hashes.json). The isolated retained-object search root and dependency search paths are recorded in every receipt; no runtime shim or toolchain modification was used.

The common exclusive lease was held continuously from **2026-10-18T02:29:44.969275Z** through verified release at **03:20:28.254360Z**, device **33**, inode **3849**, supervisor PID **277612**. All 206 attempt UUIDs and child PIDs are unique; their intervals do not overlap. Every child was owned-wait4 reaped with matching terminal waitid status, and kernel ECHILD was verified before lease release. No other worker was created. [batch-lock.json](batch-lock.json) and the per-attempt receipts retain the raw timing and ownership evidence.

There was exactly one initial/final full frozen-input preservation pair. Both cover **82,856 bindings**. The sole canonical `inputs.jsonl` is **30,291,616 bytes**, SHA256 **`0c7e38ad5b0db85c1bc9b32b958dd036639e920ff6cfbfd1f6db9445dddea460`**. Initial verification completed at **02:30:21.067535Z**; final verification completed at **03:20:24.326825Z**, attempted all paths and recorded no changes. Source/import membership, dependency pins, original objects/resolutions and small source/harness hashes were also checked between children. New outputs were separately bound in the append-only output ledger. Full final preservation occurred before releasing the continuous lease; subsequent reconciliation is offline source/log/hash checking, not another full frozen-input pass.

## Actual capacity and unchanged guards

Fixtures were not used as capacity evidence. The initial real visible headroom was below admission. The existing approved bootstrap advice increased the observed headroom from **232,583,168** to **5,344,563,200 bytes**. Following the full initial preservation pass, one renewed finite extension pass over exactly the previously approved paths restored actual first-replay admission headroom to **5,243,064,320 bytes**; first replay pre-exec headroom was **5,238,579,200 bytes**.

Default gates applied throughout; the historical 4.375 GiB exception did not apply:

| Stage | Required visible admission and pre-exec | Lowest actual admission | Lowest actual pre-exec |
| --- | ---: | ---: | ---: |
| Compile, including aggregate | 3,221,225,472 | 3,619,155,968 | 3,614,523,392 |
| Resolve | 3,221,225,472 | 3,619,057,664 | 3,614,994,432 |
| Replay | 4,294,967,296 | 4,316,663,808 | 4,311,433,216 |

All values are bytes. Host admission/pre-exec required 3 GiB separately. Runtime visible/host floor remained 1 GiB; sampled RSS stop 6 GiB; per-cgroup anonymous-growth stop 3 GiB, never summed across ancestor cgroups. AS remained 12 GiB soft/hard, CPU 60 s, wall 90 s, file size 16 MiB and core zero. Owned wait4 matching, first-failure stop, 100 ms sampling and all other guards remained unchanged.

Across **10,404 decision samples**, lowest visible headroom was **1,799,467,008 bytes**. Maximum sampled shared-mm RSS was **3,524,943,872 bytes**; maximum wait4 RSS was **3,450,952 KiB**. RSS was never summed across TIDs. These are intermittent observations, not a continuous hard RSS cap; Lean `-M` is not a kernel heap cap, and visible-ancestor accounting retains its existing partial-visibility qualification. [resource-metrics.json](resource-metrics.json) gives stage-specific minima, peaks and the actual memory-reread event.

Advice scopes were unchanged: bootstrap used the existing 66,961 dependency/tool and 7,129 preserved-data bindings. The initial integrated finalized-data subset remained 2,905 files / 1,204,978,029 bytes. The one renewed extension remained 3,809 recorded archives / 818,684,031 bytes plus 708 finalized-data files / 385,582,329 bytes. Afterward, **120 ordinary legacy-only passes** reused only previously verified eligible identities; the archive/data extension was not repeated. No current-batch, repair-checkpoint or broader filesystem paths were added to advice eligibility. Nominal advised bytes were never treated as reclaimed capacity: each admission and pre-exec used fresh actual accounting. Raw advice records preserve OOM/PID-event comparisons and before/after observations.

## Lifecycle and diagnostics

The approved narrow lifecycle handling was used throughout. There were **12 FD-transition rereads** and **one missing-memory reread**. The latter occurred during NativeWeightTransport compilation, attempt `b4325cda034e445ab966dabd2d3c6e83`: fresh stat/status for TID291785 supplied positive exiting/no-mm evidence, with both captures and timestamps preserved. Its effective classification used the fresh row; bounded grace and subsequent owned whole-process confirmation remained required. This did not use missing fields, a zombie leader or eventual exit zero alone as completion evidence. Only specifically bound original-leader memory-field errors were resolved; unrelated errors remained fatal under the unchanged policy.

The new CorePartitionBudget replay is attempt `560d886e4f17427799d5468f4c900c79`, owned child PID **277704**, exit zero with matching waitid/wait4 status and sampled peak RSS **1,246,195,712 bytes**. It had no reread in this execution. Its accepted object remains **83,848 bytes**, SHA256 **`1767dd8c642b0f2f8bf31119c76e9ce8a9a8464bd46eca8534175e2b21fcd233`**. Its compilation and existing exact singleton resolution were reused.

There were **zero failed new stages** and **zero actual Lean warning headers**. The warning counter recognizes diagnostic headers rather than counting occurrences of the word `warning` or hints. Raw allocator and Lean/checker output remain unchanged. Every successful replay's raw output is exactly its singleton `replaying <module>` line. The original rejected Core replay `0fd875cd7cf646acbb0b8453db16a991` remains `state=failed`, `exit=0`; its raw log, mixed snapshot and source-bound receipt are untouched. Both earlier failed fixture setup attempts and their harness versions also remain preserved.

## Evidence and remaining review boundary

Offline reconciliation verified all **1,269 prior production evidence entries**, all **445 approved repair evidence entries**, and all original **417 object / 346 resolution** identities and hashes. New preserved-object and resolution copies match the final root. The result and subsequent publication commit are additive and carry `[skip ci]`. The complete evidence manifest binds the raw logs, all receipts and samples, source snapshots, inventory, plans, retained output payloads, resolution files, resource records and this report.

`verify_publication.py` is an offline post-execution source/log/hash reconciler, added after the frozen runtime completed. It prints findings without overwriting the saved result and is not part of the tested runtime harness. The saved initial reconciliation output is [reconciliation.log](reconciliation.log); publication verification output is retained separately. No compiler/checker is invoked by these helpers.

Terminal checks confirm no active Lean/Lake/checker/tracer and a free common lock. The saved post-hashing idle observation had 110,161,920 bytes of visible headroom and 5,433,466,880 bytes of free disk; this is not an admission pass for any future run. Raw accounting is retained in `terminal-environment.json`. The worker pauses for independent review. **Full clean/provenance validation, final exhaustive owner/axiom audit, mathematical-hypothesis review and whole-paper acceptance remain separate.** No new theorem or hypothesis-discharge claim is made by this validation batch, and no website was changed.
