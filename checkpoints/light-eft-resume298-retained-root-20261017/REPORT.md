# Retained-root Light EFT resume: 23 chains completed; runtime headroom stop

The authorized **298-stage retained-root continuation** passed **67 stages** and completed **23 module chains**, then stopped at its first runtime failure during `LightEFTSpanners.BernoulliFlagEncoding` compilation. At **20:23:39.522527 UTC**, actual visible headroom was **1,073,291,264 bytes**, below the unchanged **1,073,741,824-byte (1 GiB) running floor** by **450,560 bytes (440 KiB)**. The supervisor sent SIGKILL; the child was reaped with exit `-9`.

Actual counts: **68 tool children/receipts**, **67 passed stages**, **one failed compilation attempt**, **230 later stages skipped**. There were 22 successful new compilations, 22 exact resolutions and 23 successful singleton kernel replays. RetainedGraph used its accepted compilation and exact existing resolution, receiving only its remaining checker. No previously qualified seed was recompiled or replayed. No retry, cap increase or scope expansion followed the runtime stop.

Final full preservation matched **all 75,320 bindings** under the same lease. All children were reaped; the lock is free. The 23 completed chains are qualified incremental results awaiting independent review. The failed compilation has no object and no completed chain; this is a physical-headroom stop, not a proof diagnostic, mathematical counterexample or whole-paper acceptance.

## Immutable source and chosen 298-stage plan

Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
Base evidence: `58caa18fbbc63af9692864e5b0cd9ffbf09b5d6e`.
Branch: `light-eft-spanners-checkpoints`; additive publication commits use `[skip ci]`.

The user reports independent acceptance of RetainedGraph compilation and exact resolution at the base evidence commit. Its checker never spawned in that attempt. The earlier 71 qualified chains retain their independent review. This records prior source/log/hash reconciliation, not repeated execution of those stages. All prior reports and failed attempts remain unchanged.

The existing output/search root was retained exactly:
`/workspace/light-eft-verification/.lake/light-eft-batch100-entries72-171-20261017-ee496fe7834c4e86994b3933112caff7`.


Initial membership was exactly **72 objects** (71 qualified seeds plus the accepted RetainedGraph compilation), **one RetainedGraph resolution JSON**, and the expected directories. The old ledger, every original object content/identity, resolution content/identity, no-symlink condition and exact file/directory membership were checked before execution. `retained-root-binding.json` records that baseline. The new batch preserved every original object and the original resolution while adding only planned objects and resolution files.

RetainedGraph's object remains **179,760 bytes**, SHA256 `cc0b144c0fc7200ffd967621d4319d9d2c9850442e9a1aea325bb1f53abba6a7`. Its resolution still names the same object at the same absolute path. No fresh root or resolution repeat was needed: the selected schedule was **one RetainedGraph singleton replay plus 99 compile/resolve/replay chains = 298 stages**, rather than 299. The driver explicitly prohibits RetainedGraph recompilation or re-resolution. All 71 qualified seeds are excluded from execution targets.

`PLAN.json` retains the source slice entries **72–171 inclusive**, RetainedGraph through `LightEFTSpanners.StoredPreparedCandidateOriginal`. The immutable graph has 486 rows, SHA256 `262e8af8f758f8d7224e8b1e7a87b4b4e8c47aab31098df3fd253af7cdbcf24c`. Source/Git bindings and exact stage counts were checked. Binding validation alone does not mean skipped sources passed execution.

The original root now contains **94 objects**: all original 72, unchanged, plus 22 new successful compilations. There is no BernoulliFlagEncoding object or residual partial output. `output-records.jsonl` binds the object versions; the final root membership is exactly those objects and the 23 accepted resolution files. `source-toolchain-object-hashes.json` records sources, tools, outputs and all nine dependency revisions.

## Finite authorized cache-advice extension

Only the accepted manifests for these two checkpoints supplied the added data scope:

- `light-eft-batch18-effective-reread-20261017`, accepted manifest at `fb2f9b7773f79a8b6ecb6365aa37d49111233150`.
- `light-eft-batch50-entries22-71-20261017`, accepted manifest at `07f6e973afde4db199ac85f0ab31663948b0b5a2`.

The selector accepts only `attempts/*/{receipt.json,samples.jsonl,raw.log}` and these seven finalized top-level data files: `inputs.jsonl`, `output-records.jsonl`, `cache-advice.jsonl`, `result-reconciliation.json`, `module-status.json`, `source-toolchain-object-hashes.json`, `publication-checks.json`. The resulting distinct set was **exactly 623 files and 234,041,133 bytes**, never exceeding its authorized ceiling. No broader data inventory hunt occurred. Code, executable/binary/object payloads, symlinks and changed/nonregular files are excluded from this extension. Existing reviewed dependency/tool and historical data advice scopes were unchanged.

`finalized_scope.py` integrates the extension into full initial preservation. It verifies both manifest hashes against the accepted bindings, fixes the allowed subset, opens each selected file without following a symlink, rejects symlink parents/nonregular/executable mode, streams its manifest-bound content hash, checks size and same-file identities, and issues ordinary per-file POSIX_FADV_DONTNEED on that same verified descriptor. It checks identity again after advice. New rows then participate in ordinary identity checks and final full content verification. Subsequent idle advice reuses those verified content/identity bindings rather than rehashing each file.

The extended initial pass verified and advised all **623 files / 234,041,133 bytes**. `expanded-scope-selection.json`, `expanded-scope-verified.jsonl` and `expanded-scope-initial.json` preserve the selection, each binding and raw accounting. The initial accounting interval includes other full-preservation reads, so its counter difference is not attributed solely to advice. Nominal file sizes are never credited as reclaimed memory.

The combined eligible set remains exactly 66,961 reviewed ordinary dependency/tool files, 7,129 historical data files and 623 added finalized data files: **12,024,908,981 nominal bytes**. There were **35 ordinary combined idle passes**, reusing the same bindings, with raw measured before/after capacity. The new category remains 623 distinct files across those passes; reuse did not add targets. The original pre-initial bootstrap used its existing reviewed scope only.

The authorized extension allowed RetainedGraph's checker to pass the unchanged gate using actual measurements:

| First checker decision | Actual visible headroom | Required gate |
| --- | ---: | ---: |
| Admission | 4,444,446,720 | 4,294,967,296 |
| Pre-exec | 4,439,908,352 | 4,294,967,296 |

These are actual fresh samples, not nominal cache-size credit. Later admission checks also remained mandatory. No additional advice or retry occurred after the failed runtime decision.

## Reviewed supervisor and exact toolchain

The reviewed supervisor, effective-reread lifecycle handling, launcher, telemetry, accounting, original preservation implementation and ordinary advice implementation are byte-identical to the accepted base. The new initial-preservation subclass adds only the explicitly authorized manifest-bound data handling described above; that integration and this new checkpoint await independent review. No lifecycle fixtures or diagnostic pilots were rerun. The historical supervisor scope label is retained unchanged; the plan and exact argv/module fields describe the actual continuation.

Official Lean remains **4.34.0**. SHA256:

- lean executable: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- leanchecker executable: `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`.
- Exact-resolution script: `9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf`.

Mathlib remains `5ed2965256430c3649e86755f9576b54eca72435`; all nine dependencies match lake-manifest and clean tracked sources. No proof source, pin, runtime shim, network/security setting or website changed.

## Completed individual chains

Each replay below is a separate official `leanchecker -v MODULE`, exit 0, with source/object binding and owned waitid/wait4 agreement. RetainedGraph reuses its previously accepted compile/resolution; every other completed row ran all three stages here. Times span only the stages in this resume, on 2026-10-17 UTC.

| Graph entry | Module | UTC start–end | Replay UUID |
| ---: | --- | --- | --- |
| 72 | LightSpanners.RetainedGraph | 20:09:24.387164–20:09:37.781941 | `4ca2fd7a9445421dbaa910fd94f710c2` |
| 73 | LightSpanners.BucketPrefix | 20:09:37.788817–20:10:11.736290 | `d66e32a000d14cc690aefe3faa83808a` |
| 74 | LightSpanners.ChordPrefix | 20:10:11.743664–20:10:45.366244 | `df6f11b12ab74d3ba2238254de1d00f1` |
| 75 | LightSpanners.MediumCounting | 20:10:45.376049–20:11:19.488011 | `56458b3301bd478b8823be7a8bb1f221` |
| 76 | LightSpanners.EndpointSampling | 20:11:19.494311–20:11:52.778780 | `ab3503c222344c16b5829d9fc97212df` |
| 77 | LightSpanners.SamplingCounting | 20:11:52.785430–20:12:30.019222 | `9456ad5b4be5430bb4bbbdeb0b5c9c6f` |
| 78 | LightSpanners.VertexCopies | 20:12:30.025984–20:13:06.215847 | `94870431799347ce8c4e4739a0563baa` |
| 79 | LightSpanners.CopyWeights | 20:13:06.222008–20:13:40.418950 | `4ccac891c4a84d75aade96d5ee0e1426` |
| 80 | LightSpanners.TreeTour | 20:13:40.425503–20:14:14.345371 | `e4a4c9a2fb584baba5ce1c712ad3023a` |
| 81 | LightSpanners.CycleReduction | 20:14:14.352365–20:14:47.957971 | `707c0fa7d3eb4314b7d7f1e545536e99` |
| 82 | LightSpanners.LightnessBound | 20:14:47.964575–20:15:24.473026 | `91a1750636de4714bc8bb02732ea61be` |
| 83 | LightSpanners.MainTheorem | 20:15:24.479374–20:16:04.263489 | `faff9e4e2d7c4b0f93bf9b9279831cfa` |
| 84 | LightEFTSpanners.StretchParameters | 20:16:04.270384–20:16:43.960160 | `ca0960ab1188433798b0dd2b38b94bf8` |
| 85 | LightEFTSpanners.ExtremalLightnessSpectrum | 20:16:43.968085–20:17:22.902226 | `ee9fb66ff16946c795d4c1a745d528a3` |
| 86 | LightEFTSpanners.TreePruning | 20:17:22.909945–20:17:59.285952 | `9d5798b0dbd24007af0ac1e862d8f104` |
| 87 | LightEFTSpanners.GraphPruning | 20:17:59.292639–20:18:33.391059 | `85d18b1b466c4726a8ec1e7850b264b1` |
| 88 | LightEFTSpanners.WeightedSampling | 20:18:33.398097–20:19:13.016257 | `d7acc7d34eba4e08b8b6a5c7c8ca35fa` |
| 89 | LightEFTSpanners.HostGraphSampling | 20:19:13.024182–20:19:55.489883 | `a3481a8f2a244b95842b4e961b1f3358` |
| 90 | LightEFTSpanners.HostLocalBlocking | 20:19:55.496392–20:20:37.699495 | `15e511b7f2264223a6853862a81cbc6d` |
| 91 | LightEFTSpanners.ExtremalHostBound | 20:20:37.706910–20:21:19.900728 | `593cf9b82e5044aeb82a9fcd97efef66` |
| 92 | LightEFTSpanners.InducedExtremalHost | 20:21:19.909892–20:22:03.045395 | `74ede78b389e4657add9a4d491921a8b` |
| 93 | LightEFTSpanners.SampledHostExtremal | 20:22:03.053232–20:22:45.456919 | `8570d79d4e784a97ab9b8e80241684d0` |
| 94 | LightEFTSpanners.AssignedHostExtremal | 20:22:45.463534–20:23:28.024826 | `af6adf4a297e4e099e7d083599ab1513` |

`module-status.json` describes every reused, passed, failed and skipped phase. `result-reconciliation.json` lists all 68 exact argv/environment combinations, UUIDs, PIDs, source hashes, UTC/monotonic times and compact metrics. Successful new compiler/resolver flags remained `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`, with the correct source root and retained output path. All compiler attempts confirmed `arena_reserve: 131072 KiB` through compile-only allocator verbosity. Checkers used supported one-thread/stack environment without compiler CLI flags. New resolutions verified exactly one target object in the retained root, excluding shadow/prefix expansion.

All 68 raw logs have **zero anchored Lean warning headers**. Allocator options/statistics are classified separately. The failed compiler's truncated execution and allocator-only output are preserved; absence of a Lean diagnostic does not establish that the unfinished proof would pass.

## First runtime failure, fully preserved

Graph entry **95**, `LightEFTSpanners.BernoulliFlagEncoding`, failed during compilation. Attempt UUID **`290f22a3ff7e4458813bb701800985e1`**, child PID **189374**, receipt interval **20:23:28.032240–20:23:43.543782 UTC**. Admission had **4,416,040,960 bytes** visible headroom and pre-exec had **4,412,342,272**, passing the 3 GiB compiler gate. The later runtime decision had:

| Stop input | Bytes |
| --- | ---: |
| Visible headroom | 1,073,291,264 |
| Required running floor | 1,073,741,824 |
| Shortfall | 450,560 |
| Identity-checked observed shared-mm RSS | 3,407,331,328 |
| RSS stop ceiling | 6,442,450,944 |
| Host MemAvailable | 17,029,275,648 |

The recorded policy error is `MemoryGuardError('Visible headroom below required floor')`. RSS was below its separate ceiling; no proof/source failure is inferred. `runtime-stop-sample.json` contains exactly the same JSON value as the receipt stop/latest sample and last telemetry line, including complete raw process/accounting inputs. The signal timestamps follow capture and precede persistence; SIGKILL was sent to the owned group, and the recorded child exit is `-9`. The full traceback, allocator log, source snapshot and failed receipt remain preserved. No BernoulliFlagEncoding object was produced. Its resolution/replay and all later module stages were skipped, totaling **230 unattempted stages**.

Controls remained AS 12 GiB soft/hard, CPU 60 seconds, wall 90 seconds, file size 16 MiB, core zero, sampled RSS stop 6 GiB and per-cgroup anonymous-growth stop 3 GiB. Compiler/resolver admission/pre-exec remained 3 GiB visible; checker visible gate remained 4 GiB; host admission remained 3 GiB; runtime visible/host floor remained 1 GiB. Shared-mm RSS and ancestor growth are never summed. Sampling is not a continuous hard RSS guarantee, and Lean `-M` is not a kernel heap cap. No cap, scope or guard changed after failure.

## One continuously held lease and final preservation

Supervisor PID `183930` held the original common lock (device 33, inode 3849, FD 3) from **2026-10-17T20:08:48.470510+00:00** through **2026-10-17T20:24:11.978275+00:00**. All 68 UUIDs and child PIDs are unique, receipt intervals do not overlap, all children were reaped and kernel ECHILD preceded release.

Initial full verification completed at **2026-10-17T20:09:20.535496+00:00**. Final full verification completed at **2026-10-17T20:24:08.163284+00:00**, attempted and matched all **75,320** paths with no changes. The batch ended at **2026-10-17T20:24:11.978436+00:00**.

The sole canonical `inputs.jsonl` is **27,666,393 bytes**, SHA256 **`39017e8025eefba2c7470e4881408f0078226f5f7fabc5f156d3f743d4d01cda`**. There was one full initial and one full final input-content pass. Compact between-child checks cover identities, source/harness hashes, pins, original and newly added objects/resolutions, and expected membership. Source snapshots are deduplicated; no full inventory is copied per child. Publication reconciliation hashes the inventory file, small bindings and evidence/objects, not every frozen dependency/data path again. It performs no extra full input-content pass.

Terminal readings in `terminal-environment.json`: disk free **7,760,404,480 bytes**, host MemAvailable **17516456 kB**, visible cgroup current **17048956928** against limit **17179869184**. No compiler/checker/tracer is running; the original lock is free. Host availability does not substitute for visible headroom, and terminal file cache reflects the final hash pass.

## Publication and remaining qualifications

`verify_publication.py` is an offline helper added after execution. It reconciles the retained root, exact 298-stage schedule/prefix, original object/resolution preservation, 623-file authority and ceilings, initial same-FD bindings, combined advice scope, all 68 receipts, raw singleton outputs, limits/locks, non-overlap, cleanup, exact runtime stop and final full preservation. Its initial saved result is `reconciliation.log`. No compiler/checker, fixture, cache advice, proof repair or retry occurred after the runtime stop.

`PUBLICATION.json` binds the result commit; the following publication commit binds that file and `evidence-sha256.json`. The manifest covers new reports, raw receipts/logs/samples, scope/control/source snapshots, 94 object payloads and compact status, excluding itself and bytecode caches. Prior evidence remains referenced at immutable commits. Raw whitespace diagnostics and exact source/data exclusions are retained in `publication-checks.json` rather than changing original bytes.

The prior 71 qualified chains retain their independent review. The 23 resumed chains, the new finite-scope integration and failed attempt await review. Dependency-cache archive authentication remains historically incomplete; accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`. Exhaustive recursive owner/axiom audit, coordinated full-clean CI and paper-level review remain outstanding. No new exhaustive audit or CI ran; mathematical hypotheses are unchanged. This is not whole-paper acceptance or completion.

Paused after publishing the actual partial result with CI skipped, no compiler/checker process and the common lock free.
