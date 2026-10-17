# Light EFT entries 72–171: RetainedGraph compiled/resolved; checker admission refused

The authorized 100-module/300-stage batch **stopped on its first failure**. `LightSpanners.RetainedGraph` compilation and exact singleton resolution passed. Its checker admission then measured **4,255,289,344 bytes** of visible headroom against the unchanged **4,294,967,296-byte (4 GiB)** gate: a shortfall of **39,677,952 bytes** after the approved scoped advice pass. **No checker child was created.** Host MemAvailable was 17,676,820,480 bytes, which does not substitute for visible headroom.

Actual counts: **three stage receipts, two tool children, two passed stages, one failed admission, zero kernel replays, zero completed new chains and 297 later stages skipped**. The remaining 99 modules were not executed. No retry, second admission/advice attempt, cap increase, fixture rerun or diagnostic pilot followed. The original 71 independently accepted qualified chains remain preserved; the new compilation/resolution are partial results awaiting review, not a completed chain.

Final full preservation matched **all 74,688 input bindings**, with no changes, before the common lock was released. All spawned children were reaped; kernel ECHILD and the free terminal lock are recorded. This is a resource-admission blocker, not a proof diagnostic or a lifecycle failure. No mathematical counterexample is inferred.

## Exact source, plan and prior review

Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
Base evidence: `07f6e973afde4db199ac85f0ab31663948b0b5a2`.
Branch: `light-eft-spanners-checkpoints`; additive publication commits use `[skip ci]`.

The user reports independent acceptance of all 150 preceding stages at the base evidence commit, bringing the accepted total to 71 qualified module chains. That records prior source/log/hash review, not new execution here. All previous receipts, failed attempts, objects and publications remain unchanged.

`PLAN.json` asserts exactly 100 new modules and 300 compile–exact-resolution–singleton-replay stages for frozen graph entries **72–171 inclusive**, `LightSpanners.RetainedGraph` through `LightEFTSpanners.StoredPreparedCandidateOriginal`. The graph is `checkpoints/light-eft-linked-rows-pilot-20261017/evidence/source-graph.json`, SHA256 `262e8af8f758f8d7224e8b1e7a87b4b4e8c47aab31098df3fd253af7cdbcf24c`, with 486 rows. Boundaries, all 100 source/Git bindings and project-import closure against the 71 seeds and earlier rows were verified before execution. Source binding verification is not compilation/replay acceptance of the skipped rows. `preparation-checks.json` records these checks and initial capacity/worker exclusion.

## Unchanged reviewed implementation and 71 seeds

The independently reviewed supervisor, effective-reread lifecycle implementation, telemetry, launcher, accounting, preservation and advice helpers are byte-identical to the accepted base. No lifecycle fixture or diagnostic pilot was needed or run. The historical supervisor scope label is retained unchanged; the actual authorization is the 100-module/300-stage plan and exact receipt module/argv fields. All original caps and guards remain in force.

The 71 hash-bound accepted seed objects match graph entries 1–71 and are disjoint from the new module names. They were copied into a fresh output root, not recompiled or replayed. Old project object roots are excluded from search; only the new root and pinned dependency/toolchain roots are used.

Fresh root:
`/workspace/light-eft-verification/.lake/light-eft-batch100-entries72-171-20261017-ee496fe7834c4e86994b3933112caff7/objects`.


The 71 seeds and one newly compiled object give **72 preserved project objects**, all bound in `output-records.jsonl` and `source-toolchain-object-hashes.json`.

New partial output:

- RetainedGraph source SHA256: `a6df38127c0480d48e619c108cd69d8cbaefed7a492f7498551001205d84c1ab`.
- RetainedGraph object: **179,760 bytes**, SHA256 `cc0b144c0fc7200ffd967621d4319d9d2c9850442e9a1aea325bb1f53abba6a7`.
- Exact resolution succeeded against this object in the new root. There was no kernel replay.

Official Lean **4.34.0** is unchanged. Executable/script SHA256:

- lean: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- leanchecker: `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`.
- Exact-resolution script: `9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf`.

Mathlib remains `5ed2965256430c3649e86755f9576b54eca72435`; all nine pinned revisions and clean tracked-source states were checked. No proof source, dependency pin, runtime shim, network/security setting or website changed.

## Exact attempts and diagnostics

| Stage | UUID | Child PID | UTC start–end, 2026-10-17 | Outcome |
| --- | --- | ---: | --- | --- |
| compile | `6d2a8ffc55aa4b359cdc163ba59de95c` | 182741 | 19:51:30.582889–19:51:42.849896 | passed, exit 0 |
| resolve | `ab1854ff7bc74b929800455ff99eecf3` | 182819 | 19:51:42.859664–19:51:54.090052 | passed, exit 0 |
| replay | `585df24493c04bf584079a501c1c57f4` | none | 19:51:54.698573–19:52:04.087430 | admission refused before spawn |

Compilation and resolution used `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`, with the exact source root and fresh output path. Compilation confirmed `arena_reserve: 131072 KiB` through compile-only verbosity. The successful resolver raw output is exactly:

```text
PASS: official checker resolution is exactly [LightSpanners.RetainedGraph]
```

Both executed children have zero anchored Lean warning headers. Mimalloc statistics/options are allocator diagnostics, not Lean warnings. Each executed child has actual inherited-limit/lock readbacks, source-bound receipt, raw log, telemetry, owned waitid/wait4 agreement and complete cleanup.

The planned checker command was `leanchecker -v LightSpanners.RetainedGraph`, with supported one-thread/stack environment. Its receipt contains the exact planned argv and source/object resolution, but **no child PID, exit status, launcher handshake, pre-exec sample, raw checker log or runtime sample file exists**, because admission was refused before process creation. Missing checker logs are not erased output. An offline inspection encountered the expected missing raw.log; that FileNotFoundError is preserved in `inspection-diagnostics.json`, not classified as a Lean failure.

The raw failure is `MemoryGuardError('Visible headroom below required floor')`. Its full measured accounting is in the failed receipt's `admission`, with the complete traceback in `invocation.log`. `result-reconciliation.json` links all three receipts; `module-status.json` records the refused replay and all 99 wholly skipped modules. No other stage was launched.

## Resource admission evidence

The scoped advice authority remained exactly 66,961 ordinary dependency/tool paths and 7,129 previously accepted data paths, 11,790,867,848 bytes per pass. No new targets or expanded scope were used. One pre-initial streaming pass used accepted prior canonical inventory SHA256 `6a366f1acfa3f8824ce90a210ba55e3d28ac0cac8a70fff1ac1e41a5fbb1b4bd`; new full verification still preceded any Lean child. It measured visible headroom 206,733,312 → 4,503,080,960 bytes.


There were exactly two between-child advice passes, one for compilation and one for the refused replay. The resolver had sufficient measured capacity and did not request advice.

| Admission | Visible before advice | Visible after advice / decision | Required visible gate | Result |
| --- | ---: | ---: | ---: | --- |
| compile | 1,130,496 | 4,258,181,120 | 3,221,225,472 | passed |
| resolve | not needed | 3,230,597,120 | 3,221,225,472 | passed |
| replay | 3,231,109,120 | 4,255,289,344 | 4,294,967,296 | refused, no child |

Raw memory.stat, before/after counters, actual file identities and scope digests are retained in `bootstrap-recovery.json`, `cache-advice.jsonl` and receipts. Advice promises no reclaimed amount. The actual post-advice checker decision remained below its gate, so no further advice or admission retry was attempted. The visible reading does not establish a unique cause or the state of unseen ancestors.

Controls remain AS 12 GiB soft/hard, CPU 60 seconds, wall 90 seconds, file size 16 MiB, core zero, sampled RSS stop 6 GiB and per-cgroup anonymous-growth stop 3 GiB. Compile/resolve visible admission and pre-exec gate remain 3 GiB; checker visible gate remains 4 GiB; host gate remains 3 GiB; runtime visible/host floor remains 1 GiB. Shared-mm RSS and ancestor anonymous growth are never summed. No cap or guard changed. Sampling is not a continuous hard RSS guarantee; Lean `-M` is not a kernel heap cap.

## Final preservation and free terminal state

Supervisor PID `182665` held the original universal lock (device 33, inode 3849, FD 3) from **2026-10-17T19:50:57.538503+00:00** through **2026-10-17T19:52:30.277235+00:00**. Three unique attempt receipts are sequential; only two children were spawned and both were reaped. The refused attempt also verified kernel ECHILD. Final preservation and all cleanup preceded release.

Initial full content verification completed at **2026-10-17T19:51:27.270648+00:00**. Final full content verification completed at **2026-10-17T19:52:26.543387+00:00**, attempted and matched all **74,688** paths with no changes. The batch ended at **2026-10-17T19:52:30.277529+00:00**.

The sole canonical `inputs.jsonl` is **27,414,247 bytes**, SHA256 **`233119bca6c5aaae60ca9ee555a6da3a22bd6cd5e52d97081fab1186b57e6fec`**. There was one full initial and one full final input-content pass. Between stages, compact identity/search-membership, pin, small-source/harness and output/resolution checks ran. Source snapshots are deduplicated by hash. Publication reconciliation reads the canonical inventory file and small source/control/evidence/object bindings, not all frozen dependency path contents again; no third full input-content pass occurred.

Terminal readings in `terminal-environment.json`: disk free **7,897,702,400 bytes**, host MemAvailable **17496088 kB**, visible cgroup current **16985968640** against limit **17179869184**. No compiler/checker/tracer is active and the original common lock is free. Final hashing repopulates file cache; terminal host availability is not substituted for checker admission capacity.

## Publication and remaining qualifications

`verify_publication.py` is an offline helper added after the stop, not part of the tested harness. It verifies graph/source bindings, reviewed helper byte identity, all three receipts, the before-spawn refusal, successful child cleanup, seed/object hashes, unchanged advice scope, final preservation and free terminal state. Its saved initial result is `reconciliation.log`. No proof repair, retry, fixture, extra compiler/checker or extra full input-content pass was performed after the stop.

`PUBLICATION.json` binds the result commit; the following publication commit binds that file and `evidence-sha256.json`. The manifest covers all new checkpoint evidence except itself and bytecode caches. Prior evidence is referenced at its immutable commits, without copying full inventories per child. Whitespace diagnostics and exact preserved-data exclusions are recorded in `publication-checks.json`; raw/source bytes remain unchanged.

The current blocker is the unchanged checker's measured visible admission gate. There are no newly completed module chains and no new kernel replay result. The accepted 71 chains retain their prior review; RetainedGraph compilation/resolution remain partial results awaiting independent review. Dependency-cache archive authentication remains historically incomplete; accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`. Exhaustive recursive owner/axiom audit, coordinated clean CI and paper-level review remain outstanding. Mathematical hypotheses are unchanged. No whole-paper acceptance/completion is claimed.

Paused after publishing the actual partial outcome with CI skipped, no compiler/checker process and the common lock free.
