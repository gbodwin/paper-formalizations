# Light EFT: effective-reread repair and all 53 continuation stages passed

All **53 authorized stages passed**: 17 compilations, 18 exact singleton resolutions and 18 individual official kernel replays. All 18 continuation module chains passed final full preservation of **74,625 input bindings**. No stage was retried or skipped; none of the four accepted project objects was recompiled. This is a qualified incremental validation checkpoint awaiting independent review, not clean CI, a final exhaustive axiom audit or paper-level acceptance.

## Source and prior review

Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
Base evidence: `0e5cbc36d193e89c5a114e46377c52c459f46f84`.
Branch: `light-eft-spanners-checkpoints`; publication commits use `[skip ci]`.

The user reports independent acceptance of the qualified AdaptiveFiniteLaw and FiniteHoeffding chains at the base evidence commit, together with ProductSampleConcentration compilation. That is prior source/log/hash review, not fresh execution in this checkpoint. Its failed resolver receipt remains failed and unchanged in the prior checkpoint. Here ProductSampleConcentration receives a new exact resolution and singleton replay; its accepted compiled object is reused byte-identically.

The initial fresh object root contains exactly four preserved objects:

| Object | Bytes | SHA256 |
| --- | ---: | --- |
| LightEFTSpanners.FiniteLaw | 254600 | `04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc` |
| LightEFTSpanners.AdaptiveFiniteLaw | 122416 | `3dd736d2a646495a70baafd47334f13455fb80c66a9bc454c583d5460b3c33c0` |
| LightEFTSpanners.FiniteHoeffding | 253688 | `44c7650836db9eca216944513df76b48e9fd74f040d95351e72a1207238d03e8` |
| LightEFTSpanners.ProductSampleConcentration | 145664 | `37324c16372f539577e12ee4c636dd9fc135e72d2aa076a09b54ffa88c6979c8` |

`PLAN.json` fixes the 18 ordered modules and the 53-stage continuation. The new root is
`/workspace/light-eft-verification/.lake/light-eft-batch18-effective-reread-20261017-669cba2ef8e14a218cc2103ac434394b/objects`.

Old project object roots are excluded from LEAN_PATH. Existing pinned dependency/toolchain search roots are reused; the 486-source graph and all requested source/Git bindings remain unchanged. Four objects were seeded and 17 new objects compiled, giving 21 preserved object payloads in `preserved-objects/`. `source-toolchain-object-hashes.json` records exact source, executable and object hashes plus all nine dependency revisions and clean tracked-source status.

Official toolchain: Lean **4.34.0**. Executable SHA256 values:

- lean: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- leanchecker: `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`.
- Official-resolution script: `9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf`.

Mathlib remains `5ed2965256430c3649e86755f9576b54eca72435`; all nine dependencies match the unchanged lake-manifest. No proof source, pin, website, runtime shim, network or security setting changed.

## Precise lifecycle repair

`exit_transition.py` now separates preserved raw observations from effective per-TID classification. After FD loss, an identity-checked fresh read replaces that TID everywhere downstream: the effective leader reference, live candidates and exiting-only fallback. Positively disappeared siblings are removed from effective candidates, while their raw observations and disappearance evidence remain. Both the initial row and its nested FD-transition reread are retained.

The same classifier validates initial and fresh rows. Identity/ownership/start-time errors, non-memory collection errors, still-live missing memory and still-live missing lock fail closed. An exiting/no-mm reread starts or checks fixed, non-resetting one-second grace; it is never completion. Accounting, descendants, deadlines, owned waitid confirmation and the sole matching wait4 reap remain required. Identity-checked RSS observations from before and after the reread are retained for the sample maximum, peaks and ceiling checks, so teardown cannot erase an earlier breach.

The child runner, decision telemetry, resource controls, launcher and preservation implementation are byte-identical to the accepted base. The raw repair diff is `lifecycle-changes.diff`.

## Harmless fixture evidence

All **12 deterministic reread regressions** and the **14 existing lifecycle fixtures** passed before the batch. No C or Lean compilation was used. New regressions use parked real Python/pthread children, real universal leases and owned waitid/wait4, with synthetic transition/FD inputs explicitly labeled and preserved beside original proc observations. Positive cases remain pending while the real child is alive, keep the same grace deadline across a second decision, then pass only after actual kernel terminal confirmation and matching wait4.

Coverage includes the captured live-leader → FD-loss → fresh exiting/no-mm sequence; sibling reread and positive disappearance; fresh live-missing memory, identity mismatch, non-memory collection error and missing lock; earlier and fresh RSS breaches; and grace expiration. Existing fixtures again cover native leader exit with live siblings, teardown, non-resetting timeout, accounting/headroom/RSS failure, nonzero/signal exit, waitid ownership failure and sibling identity mismatch. Negative synthetic cases passing means the guard rejected them as intended; it does not mean a real child consumed 6 GiB.

See `effective-reread-fixture-results.json`, `whole-process-fixture-results.json`, their raw logs, and unique source/harness-bound receipt directories. Three production samples also exercised the repaired FD reread: ProductSampleConcentration resolution, LightEFTSpanners.Basic resolution and SamplingRestriction resolution. Their effective rows match the fresh no-mm observations, their earlier RSS observations remain, and termination was confirmed within the fixed deadline.

## Actual module results

Each listed replay is a separate `leanchecker -v MODULE`, exit 0. Full compile/resolution/replay argv, environment, PIDs, source hashes, monotonic and UTC times are in each receipt and `result-reconciliation.json`. The following times span only the stages run here; ProductSampleConcentration compilation was reused.

| Module | UTC start–end on 2026-10-17 | Replay UUID | Result |
| --- | --- | --- | --- |
| LightEFTSpanners.ProductSampleConcentration | 18:52:22.120076–18:52:50.920942 | `cf86592dacbf48f794db24fcd01ffa96` | passed |
| LightSpanners.FiniteSampling | 18:52:50.927252–18:53:27.284605 | `d1764a19e61c45cbb75ad16fbfeb9691` | passed |
| LightEFTSpanners.BlockerSampling | 18:53:27.291747–18:54:08.640049 | `764a4a99f5ed46e3bc5c44374870e2e6` | passed |
| LightEFTSpanners.SamplingFaultAvoidance | 18:54:08.646682–18:54:51.943859 | `3cda1b85280944818dd16c72eaf9ca05` | passed |
| LightSpanners.Basic | 18:54:51.950726–18:55:28.727673 | `dd032c07f1164767914491d9886a06d8` | passed |
| LightSpanners.Greedy | 18:55:28.733794–18:56:03.751775 | `935c0c775d40453a90abefd9b4d1a0f7` | passed |
| LightSpanners.Kruskal | 18:56:03.759142–18:56:38.958786 | `f35f52382ae140918b7c070368da3b9d` | passed |
| LightSpanners.MinimumTree | 18:56:38.965132–18:57:15.275302 | `4ec80c06ed4f45a9863f9a46900e48eb` | passed |
| LightEFTSpanners.Basic | 18:57:15.283273–18:57:51.259909 | `4442a0a435bd4597b8611ac4fc92a4dc` | passed |
| LightSpanners.Distance | 18:57:51.268660–18:58:26.412154 | `f2d203f9b9634038bde95960b6a8c09d` | passed |
| LightSpanners.Construction | 18:58:26.419470–18:59:01.652861 | `f8fdbff90fd4406780b867e5fcb03fe6` | passed |
| LightEFTSpanners.SeededGreedy | 18:59:01.660505–18:59:37.290263 | `245162dbd4444830be87c5ce8106e277` | passed |
| LightEFTSpanners.AlgorithmSampleProbability | 18:59:37.296259–19:00:17.307801 | `744ca9a065bd4ac9a7eed4d2678f8174` | passed |
| LightEFTSpanners.EmpiricalVotingGreedy | 19:00:17.314560–19:01:00.047814 | `e8fa52813e2d4a08a1f80e15bb7655c3` | passed |
| LightEFTSpanners.SamplingRestriction | 19:01:00.054313–19:01:44.213497 | `ebed805a117745039c558ea90543f154` | passed |
| LightEFTSpanners.BernoulliTestConcentration | 19:01:44.221150–19:02:30.438047 | `159f755de0c74e84a7a6013eb7e4f0cc` | passed |
| LightEFTSpanners.FreshVotingTapes | 19:02:30.445204–19:03:13.802877 | `0ad7ec4a922240bca26f641ecd0005c1` | passed |
| LightEFTSpanners.AdaptiveVotingConcentration | 19:03:13.810087–19:04:01.439746 | `8b44cddcef4341cc9f0d45bb7a891efe` | passed |

Compiler/resolver flags stayed `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`, using the exact source root and fresh output path. Each compile confirmed `arena_reserve: 131072 KiB` through compile-only allocator verbosity. Checkers used supported `LEAN_NUM_THREADS=1` and `LEAN_STACK_SIZE_KB=65536`, without compiler CLI options. Each resolver verified exactly one target object in the new root, including absence of prefix-expanded/shadowed targets.

All 53 raw logs have **zero anchored Lean warning headers**. Mimalloc options/statistics are allocator diagnostics, not Lean warnings. No compiler/checker failed in this continuation. Previous failed attempts remain preserved at their immutable evidence commits.

## Sequential execution, full preservation and resources

Supervisor PID `164617` held the original universal lock (device 33, inode 3849, FD 3) from **2026-10-17T18:51:46.763563+00:00** through **2026-10-17T19:04:28.451224+00:00**. All 53 UUIDs and child PIDs are unique, receipt intervals do not overlap, all direct/adopted children were reaped and kernel ECHILD preceded release.

Initial full content verification completed at **2026-10-17T18:52:18.047703+00:00**. Final full content verification completed at **2026-10-17T19:04:24.720954+00:00**, attempted all **74,625** paths, matched exactly and recorded no changes. The sole canonical `inputs.jsonl` has **27,391,841 bytes** and SHA256 **`de9b5cade136816d74bf21ec30208e802607881dace69e5b2ea641db075ab517`**. The batch ended at **2026-10-17T19:04:28.451490+00:00**.

Between children, compact identity/search-membership, pin, small-source/harness and output/resolution checks ran under the same lease. Sources are stored once by hash; no full input table is duplicated per child. There was one full initial and one full final content pass. Post-execution reconciliation hashes the canonical inventory file, small bindings and evidence/objects only; it never performs a third full input-content pass.

Idle cache advice used exactly the prior accepted scope: 66,961 ordinary dependency/tool paths and 7,129 preserved data paths, 11,790,867,848 bytes per pass. One pre-initial streaming pass used the accepted prior inventory (`c6ef74001a7bcbf35624556862f87e173ff939863d85631e253686815ad450cd`) to avoid allocating full tables before headroom recovery. New full verification still preceded all Lean stages. There were 26 between-child passes over current verified identities, with unchanged eligibility and no new targets. Full before/after accounting and actual capacity decisions remain in `bootstrap-recovery.json`, `cache-advice.jsonl` and receipts. Advice itself certifies no content and promises no reclaimed-byte amount.

Limits stayed AS 12 GiB soft/hard, CPU 60 seconds, wall 90 seconds, file size 16 MiB and core zero. Admission/pre-exec visible gates remained 3 GiB for compile/resolve and 4 GiB for checker, with host gate 3 GiB. Runtime visible/host floor remained 1 GiB, sampled RSS stop 6 GiB and per-cgroup anonymous-growth stop 3 GiB, never summed across ancestors. The observed shared-mm RSS is never summed across TIDs. Full raw accounting, including memory.stat, remains preserved. Sampling is not a continuous hard RSS guarantee, and Lean `-M` is not a kernel heap cap.

Maximum sampled RSS was **3,445,764,096 bytes**; maximum wait4 RSS was **3,472,367,616 bytes**. Minimum recorded runtime visible headroom was **1,251,561,472 bytes**. Terminal resource readings are in `terminal-environment.json` (disk free 8,211,394,560 bytes; host MemAvailable 17501696 kB; visible cgroup current 17040539648 against limit 17179869184). Final content hashing repopulates file cache; host available memory is not substituted for visible headroom.

## Publication and remaining qualifications

All execution completed before the reported `2026-10-17T19:05:55Z`
disconnect. At `19:06:56.022242 UTC`, execution access was usable, the batch
result and final preservation were intact, no compiler/checker/tracer was
running and the original common lock was free. Nothing was restarted.
`disconnect-reconciliation.json` records this pre-publication check.

`verify_publication.py` is an offline helper added after execution and is not part of the tested harness. Its initial saved result is `reconciliation.log`; `result-reconciliation.json` provides all 53 commands and compact metrics. The full checkpoint manifest binds receipts, raw logs, samples, fixture sources, control snapshots, four reused/17 new object payloads and readable status. `PUBLICATION.json` binds the result commit; the subsequent publication commit binds that file and `evidence-sha256.json`. Raw bytes and any whitespace diagnostics are retained in `publication-checks.json`.

The user-reported prior AdaptiveFiniteLaw/FiniteHoeffding review is retained. The 18 new chains await independent review. Dependency-cache archive authentication remains historically incomplete; accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`. No new recursive owner/axiom audit or CI was run. The final exhaustive audit, coordinated clean CI and paper-level review remain outstanding. Mathematical hypotheses are unchanged. This result validates the approved module continuation incrementally; it is not whole-paper acceptance.

The worker pauses after CI-skipped publication with no compiler/checker/tracer running and the original common lock free. No unrelated paper, SCC proof or website was changed.
