# Light EFT graph entries 22–71: all 150 stages and final preservation passed

All **50 new module chains** passed: **50 compilations, 50 exact singleton resolutions and 50 individual official kernel replays**. There were zero failed/skipped stages, zero retries, zero Lean warning headers and zero seed rebuilds or seed replays. Final full preservation matched **74,638 input bindings** with no changes under the same universal lease.

This is qualified incremental validation awaiting independent review. The preceding 21 module chains were independently accepted; those seeds were reused rather than executed again. Dependency provenance, exhaustive audit, coordinated clean CI and paper-level qualifications remain. No whole-paper completion or acceptance is claimed.

## Exact authorized plan and source

Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
Base evidence: `fb2f9b7773f79a8b6ecb6365aa37d49111233150`.
Branch: `light-eft-spanners-checkpoints`; additive publication commits use `[skip ci]`.

The user reports independent acceptance of all 53 prior continuation stages and the effective-reread repair, completing 21 qualified module chains including FiniteLaw. That is prior source/log/hash review, not new execution here. All earlier evidence, including failed attempts, is unchanged.

`PLAN.json` contains exactly **frozen graph entries 22–71 inclusive**, from `LightEFTSpanners.HostCounting` through `LightSpanners.BucketRestriction`. The graph is `checkpoints/light-eft-linked-rows-pilot-20261017/evidence/source-graph.json`, SHA256 `262e8af8f758f8d7224e8b1e7a87b4b4e8c47aab31098df3fd253af7cdbcf24c`, with 486 rows. The slice, all 50 source/Git hashes and import closure against the 21 seeds and earlier rows were checked before execution; `preparation-checks.json` preserves those checks.

The previous first-module compile-skip exception was removed. The driver asserts 50 new modules and 150 stages and uses the plan's compile/resolve/replay sequence for every row. HostCounting compiled as stage 001. The module and stage counts are bound to the plan rather than the old 18-module/53-stage continuation. No stage beyond entry 71 was authorized or run.

## Reviewed implementation and fresh object root

The reviewed child supervisor, effective-reread lifecycle handling, decision telemetry, preservation implementation, launcher, accounting and advice helpers were reused byte-identically. Their hashes are recorded in preparation evidence and rechecked by the offline verifier. No lifecycle fixtures were rerun solely for this new module plan. The supervisor retains its historical scope label byte-identically; the actual 50-module/150-stage authorization is in the plan and exact receipt module/argv fields.

The reviewed effective-reread behavior remains in force: raw initial and fresh observations are both retained; effective leader/live/exiting classification uses the validated fresh row; disappeared siblings leave effective candidates; earlier observed RSS remains available to peak/ceiling checks. Fresh identity, non-memory collection, still-live missing memory and missing lock errors fail closed. Fixed one-second grace, physical accounting, deadlines and owned waitid/wait4 completion remain required. No resource or safety control changed.

Exactly 21 hash-bound accepted objects were copied into a fresh root. The seed names match graph entries 1–21, and are disjoint from this batch's 50 module names. Neither compiler nor checker targeted a seed. `PLAN.json` binds every seed payload and prior acceptance evidence; their source hashes and payloads remain preserved.

Fresh output root:
`/workspace/light-eft-verification/.lake/light-eft-batch50-entries22-71-20261017-b16e5f6063ae4f2eab3230dfc55f148e/objects`.


Old project object roots are excluded from search. Only the new root and the existing pinned dependency/toolchain object roots are used. Fifty new objects plus the 21 seeds give **71 preserved project objects**. `output-records.jsonl` records compact versions; `source-toolchain-object-hashes.json` gives exact source, executable and object hashes, plus nine dependency revisions and clean tracked-source status.

Official toolchain remains Lean **4.34.0**. Executable/script SHA256:

- lean: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- leanchecker: `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`.
- Exact-resolution script: `9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf`.

Mathlib is still `5ed2965256430c3649e86755f9576b54eca72435`. All nine dependencies match the unchanged lake-manifest. No proof source, pin, runtime shim, network/security setting or website changed.

## Individual module outcomes

Each row passed compilation, exact singleton resolution and a separate official `leanchecker -v MODULE`, exit 0. Times span that row's three stages on 2026-10-17 UTC. Replay UUIDs identify the individual kernel checks; PIDs, all commands/options/environment, submitted-source hashes and monotonic/UTC timestamps are in receipts and `result-reconciliation.json`. `module-status.json` includes each final object hash.

| Graph entry | Module | UTC start–end | Replay UUID |
| ---: | --- | --- | --- |
| 22 | LightEFTSpanners.HostCounting | 19:13:46.004742–19:14:30.422953 | `cd3020b414fe4a0b8e5f65a8eef1d599` |
| 23 | LightEFTSpanners.VotingFaultWitness | 19:14:30.431203–19:15:13.690569 | `27227725e7aa414094db64329690042b` |
| 24 | LightEFTSpanners.VotingGreedyCorrectness | 19:15:13.696875–19:15:56.812141 | `0120c19bcf3349cd8ca79a284136c4c6` |
| 25 | LightEFTSpanners.Blocking | 19:15:56.818730–19:16:37.856654 | `025231120831488286df25719532dc6c` |
| 26 | LightEFTSpanners.VotingAdmissionHistory | 19:16:37.865903–19:17:20.944758 | `318613b0f9204a20be50b95c3c5046b3` |
| 27 | LightEFTSpanners.SampledHistoryCandidates | 19:17:20.952130–19:18:06.768861 | `7db5b37dd96c44b5adbdcd263d39649f` |
| 28 | LightEFTSpanners.SampledPrefixProbability | 19:18:06.776390–19:18:50.336257 | `f5d99ecb6c9944b795e2372c4b8b5ae0` |
| 29 | LightEFTSpanners.SampledHistoryWeight | 19:18:50.342337–19:19:35.089707 | `17152705c6e84531ad604e8296d187c8` |
| 30 | LightEFTSpanners.SampledHostExpectation | 19:19:35.096626–19:20:19.061939 | `02276305065745c699d688b3caf4d4c1` |
| 31 | LightSpanners.CycleProjection | 19:20:19.069143–19:20:55.716547 | `1de3c88691ea4b859b992cb420c42f20` |
| 32 | LightEFTSpanners.BlockerTransport | 19:20:55.723261–19:21:30.320177 | `ab589765177041cd968b4b2af4f9e07a` |
| 33 | LightSpanners.Girth | 19:21:30.327313–19:22:04.253344 | `66ea69f22876427491b677a5811eb6b8` |
| 34 | LightSpanners.Weight | 19:22:04.260283–19:22:38.838123 | `b67ec5c8dd8d468ebed28671a80a0359` |
| 35 | LightEFTSpanners.HostWeightTransport | 19:22:38.845302–19:23:13.177261 | `bc8bc2dea5c1468fa207d49cffbaffd6` |
| 36 | LightSpanners.Subdivision | 19:23:13.184294–19:23:47.479205 | `0407f4ad9f5b4d85a9fd5b1b0a84c6e0` |
| 37 | LightSpanners.EdgeSubdivision | 19:23:47.488436–19:24:21.537170 | `697623b5ab0e44c1bcd487da126adaf3` |
| 38 | LightSpanners.SubdivisionCycles | 19:24:21.546461–19:24:56.709850 | `bcd5e0df6a27419682d6df7c69fa2479` |
| 39 | LightSpanners.SubdivisionTree | 19:24:56.717323–19:25:32.664138 | `3475705a86ca48f4af55e9d988f4a00c` |
| 40 | LightSpanners.SubdivisionGirth | 19:25:32.671466–19:26:06.539509 | `dde7eb37669748b88a3f5844dc641868` |
| 41 | LightSpanners.RoundingTree | 19:26:06.546176–19:26:41.414987 | `78f8b17789a542f789c97339350ea9c6` |
| 42 | LightSpanners.TreeReduction | 19:26:41.421995–19:27:17.955837 | `1c136b1efbef4e51907af0ff0c84604a` |
| 43 | LightEFTSpanners.ExtremalReindex | 19:27:17.963504–19:27:52.147843 | `cfe587b4fe26432f8d6c3f11ae5b155c` |
| 44 | LightEFTSpanners.ExactOrderSubdivision | 19:27:52.154860–19:28:26.621954 | `6d8a54ccb2a7418abf847391042e9e7d` |
| 45 | LightSpanners.UnitCycle | 19:28:26.631048–19:29:00.774429 | `0885423989d846ed89d024df043466b7` |
| 46 | LightSpanners.TourCycle | 19:29:00.781277–19:29:35.194882 | `d122181e02414e7d9ed4197acbdfc01b` |
| 47 | LightSpanners.CycleOrder | 19:29:35.203098–19:30:09.664220 | `fd0ea0e36add468b89d7dfc42e1ab021` |
| 48 | LightSpanners.Counting | 19:30:09.675569–19:30:43.208034 | `674f7cb9552a43619f84b650958039c8` |
| 49 | LightSpanners.BucketPaths | 19:30:43.215310–19:31:20.226707 | `c6f325931ab44ad8b96b6e1823fe94b1` |
| 50 | LightSpanners.HikerSquads | 19:31:20.233794–19:31:54.885927 | `1011c34938ac4c5096a73e66d1ac58e1` |
| 51 | LightSpanners.BucketCycles | 19:31:54.893152–19:32:33.468755 | `db11e9b76b0441febe88d2d93f7ddd9c` |
| 52 | LightSpanners.CycleSegments | 19:32:33.475965–19:33:08.540286 | `2ad049e20454438487dc81012ec1d3ff` |
| 53 | LightSpanners.HikerLayers | 19:33:08.547223–19:33:44.387603 | `af652cec640744b2a64c2fa0ac9bee46` |
| 54 | LightSpanners.HikerCompletion | 19:33:44.394826–19:34:19.253578 | `1350725eb0074661a85889282e6ab196` |
| 55 | LightSpanners.BucketPadding | 19:34:19.261674–19:34:54.975838 | `52ef123b3b334db593767cdad7fb126b` |
| 56 | LightSpanners.CycleBalance | 19:34:54.983608–19:35:30.380732 | `613c1cf9d3394c67af68a2e4132f47c9` |
| 57 | LightSpanners.ChordWords | 19:35:30.388233–19:36:04.009956 | `945007e64a6b49da9ab871a0df2f331f` |
| 58 | LightSpanners.BucketUniqueness | 19:36:04.017638–19:36:38.757525 | `dc36f97fc13c4dd384be35811c96d853` |
| 59 | LightSpanners.MonotonePadding | 19:36:38.765797–19:37:12.014202 | `7a681ebb32ff494882e735d1f510b5db` |
| 60 | LightSpanners.PaddingPositions | 19:37:12.022204–19:37:47.345458 | `789ca17d16604776adc7e31015c965fc` |
| 61 | LightSpanners.UsefulFamily | 19:37:47.353518–19:38:21.059150 | `fbc3c13087174964bdcc417141972355` |
| 62 | LightSpanners.BridgeWords | 19:38:21.067791–19:38:55.271734 | `7d8adc43633244b8a868dde9cf015983` |
| 63 | LightSpanners.BucketBudgets | 19:38:55.279950–19:39:29.767044 | `3c8c4e862f60490c96cc09de9b743c3d` |
| 64 | LightSpanners.BucketDispersion | 19:39:29.774257–19:40:04.569161 | `69a3ef8cf0714f4691c4cf363c4b4b91` |
| 65 | LightSpanners.EndpointCounting | 19:40:04.577305–19:40:40.115816 | `650f201fb8294b6898d38a27dab54977` |
| 66 | LightSpanners.HikerDay | 19:40:40.123671–19:41:14.564228 | `e74c5671738a419491ed10e086d1a622` |
| 67 | LightSpanners.HikerTour | 19:41:14.572992–19:41:49.864473 | `aae1397bcd474403b6ed8fd33cdbdd1b` |
| 68 | LightSpanners.UnitCycleWeight | 19:41:49.872465–19:42:24.205029 | `c9dcc5153f704f178491f5f12e15e97e` |
| 69 | LightSpanners.DyadicEnumeration | 19:42:24.213930–19:42:58.364420 | `67766fb47c594168bb6c4f37211800a5` |
| 70 | LightSpanners.WeakCounting | 19:42:58.373491–19:43:32.577181 | `43b36b58d69144eeb303eddd43004dd7` |
| 71 | LightSpanners.BucketRestriction | 19:43:32.585820–19:44:06.664283 | `6d316d7a8d384a1ead6d736b5dc813e9` |

Compiler/resolver flags stayed `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`, with exact source roots and fresh output paths. All 50 compiles confirmed the 128 MiB arena through compile-only allocator verbosity (`arena_reserve: 131072 KiB`). Checkers used supported `LEAN_NUM_THREADS=1` and `LEAN_STACK_SIZE_KB=65536`, without compiler CLI flags. Each official resolution was exactly one target object in the new root, with shadowing and prefix expansion excluded.

All 150 raw logs have **zero anchored Lean warning headers**. Mimalloc options/statistics are allocator diagnostics, not Lean warnings. No production compiler/checker, supervision or resource failure occurred. Raw logs and telemetry remain byte-identical; any whitespace diagnostic is retained rather than editing raw output.

## One shared lock and two full content passes

Supervisor PID `169717` held the original common lock (device 33, inode 3849, FD 3) from **2026-10-17T19:13:10.711707+00:00** through **2026-10-17T19:44:33.445310+00:00**. All 150 UUIDs and child PIDs are unique; receipt intervals do not overlap. Each child had independent admission, pre-exec readbacks, anonymous-growth baseline, runtime telemetry and complete cleanup. Kernel ECHILD preceded release.

Initial full verification completed at **2026-10-17T19:13:42.624013+00:00**. The first stage receipt began at **2026-10-17T19:13:46.004742+00:00** and the last ended at **2026-10-17T19:44:06.664283+00:00**. Final full verification completed at **2026-10-17T19:44:29.707409+00:00**, matching all **74,638** paths with no changes. The batch ended at **2026-10-17T19:44:33.445493+00:00**.

There is one canonical `inputs.jsonl`: **27,396,538 bytes**, SHA256 **`6a366f1acfa3f8824ce90a210ba55e3d28ac0cac8a70fff1ac1e41a5fbb1b4bd`**. There was one full initial and one full final input-content pass. Between children, compact identity/search membership, pin, small-source/harness and project-output/resolution checks ran. Source snapshots are deduplicated by hash; no full input table is copied per child. Publication reconciliation reads the inventory file, small source/control bindings and evidence/object payloads only; it does not perform a third full frozen-input content pass.

Idle cache advice remained within the previously reviewed scope: 66,961 ordinary dependency/tool files and 7,129 preserved data files, 11,790,867,848 bytes per pass. One pre-initial streaming pass used the accepted prior canonical inventory SHA256 `de9b5cade136816d74bf21ec30208e802607881dace69e5b2ea641db075ab517` to recover actual headroom before allocating full input tables. It certified no new contents; the full initial pass still preceded every Lean child. There were 59 between-child idle passes over current verified identities, with no new targets, scope expansion or speculative cache credit. Raw before/after accounting and actual measured admission remain in the bootstrap/advice records and receipts.

## Resource evidence

Controls remain AS 12 GiB soft/hard, CPU 60 seconds, wall 90 seconds, file size 16 MiB, core zero, sampled RSS stop 6 GiB and per-visible-cgroup anonymous growth stop 3 GiB. Compile/resolve visible admission and pre-exec gate remain 3 GiB; checker visible gate remains 4 GiB; host admission remains 3 GiB; running visible/host floor remains 1 GiB. Anonymous growth is checked per cgroup, never summed across ancestors. Shared-mm RSS is never summed across TIDs.

Full memory.stat and raw process/accounting observations, null teardown values, owned waitid confirmations, inherited lock/limit handshakes and matching wait4 reap results are preserved for every child. Six production FD-transition rereads used fresh effective no-mm classification while retaining earlier RSS, and reached owned terminal confirmation within fixed grace. Sampling is not a continuous hard RSS guarantee; Lean `-M` is not a kernel heap cap.

Maximum sampled RSS: **2,987,454,464 bytes**. Maximum wait4 RSS: **3,004,104,704 bytes**. Minimum recorded runtime visible headroom: **1,672,478,720 bytes**. Terminal readings in `terminal-environment.json`: disk free **7,997,894,656 bytes**, host MemAvailable **17487140 kB**, visible cgroup current **17110036480** against limit **17179869184**. Final hashing repopulates file cache; host availability is not substituted for visible headroom.

## Evidence publication and remaining qualifications

`verify_publication.py` is an offline helper added after execution, not part of the tested harness. It reconciles graph slice/source bindings, reviewed helper byte identity, all 150 receipts, singleton replay outputs, limit/lock readbacks, non-overlap, reaping, fresh effective classifications, object/seed bindings, saved final preservation and idle-advice scope. Its initial saved result is `reconciliation.log`; the compact detailed stage record is `result-reconciliation.json`. No extra compiler/checker, diagnostic fixture or full frozen-input content pass was run during publication.

`PUBLICATION.json` binds the result commit. The following publication commit binds that file and `evidence-sha256.json`, covering the complete new checkpoint except the manifest itself and bytecode caches. Prior evidence is referenced at its existing immutable commits. `publication-checks.json` preserves whitespace-check output and any exact raw-data exclusions; source and diagnostic bytes remain unchanged.

The 50 new qualified chains await independent review; the 21 seed chains retain their prior independent review. Dependency-cache archive authentication remains historically incomplete. Accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`. No new exhaustive recursive owner/axiom audit or CI was run. Final exhaustive audit, coordinated clean CI and paper-level review remain outstanding; mathematical hypotheses are unchanged. This batch does not establish whole-paper acceptance or completion.

Paused after CI-skipped publication with no compiler/checker/tracer running and the original common lock free.
