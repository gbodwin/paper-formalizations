# One hash-then-advise bounded import: child failed

**Result: CHILD_FAILURE_SIGABRT_NO_IMPORT_SUCCESS.** Exactly one authorized `run_once()` call, one launcher/Lean child, no retry. UUID `6754ef8813d743d598a0524b605c858a`, child PID **151712**. Attempt created **2026-10-17T13:47:27.637961+00:00**, finalized **2026-10-17T13:48:21.237350+00:00**.

Reviewed implementation `93dfdf4daa73288af37fb8a180f5bb191939c075` and evidence `3cdea29a7714997dd95e3823924920a2c5dd7b7a` were verified before invocation. An additive copy changed only the two fixed pilot/evidence directory suffixes to `96123e1f5eb949769b71b05f9eb1a463`; [path-only.diff](path-only.diff) preserves that exact change. Helper files matched the reviewed bytes. The original runner and consumed directories are untouched; the new directories are now consumed and preserved too. Frozen production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`.

## Admission and exact outcome

The finite preflight hash/advice phase completed without error. Admission passed with visible parent limit **17,179,869,184 bytes**, current **12,104,671,232 bytes**, headroom **5,075,197,952 bytes**, above the unchanged **2 GiB** threshold. Hidden ancestor limits remained explicitly unknown. The supervisor verified the pre-exec handshake and kernel soft=hard limits: AS **1,610,612,736 bytes**, CPU **60 seconds**, FSIZE **16,777,216 bytes**, CORE **0**. The child had a new session/process group and the inherited verified universal lock descriptor.

The exact pinned official command remained `lean -j1 -M512 -DautoImplicit=false -DwarningAsError=true <fixed ImportSmoke.lean>` with source `import Aesop.Script.Tactic`, dependency-only paths and allowlisted environment. The receipt contains full absolute paths, executable/input hashes and environment. No output-object flags were used.

The child emitted this sole fatal runtime diagnostic:

```text
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable
```

It exited **-6 (SIGABRT)**. The wrapper reported `RuntimeError('Child failed before/after exec')` and exited 1. This is a runtime/startup failure, not a mathematical counterexample, Lean theorem failure, warning-only result or import success. The precise resource responsible for thread creation failure is **not established** by this receipt; neither low sampled RSS nor passing cgroup admission rules out address-space/thread constraints. No cap was changed and no further experiment was attempted.

## Caps, observations and cleanup

The 90-second child deadline, 512 MiB stop floor and all limits remained unchanged. Three monitoring samples are retained. OOM counters did not change across those samples: parent `(1,1,0)`, visible child group `(0,1,0)` for oom/oom_kill/oom_group_kill. The last sample observed the direct child as a zombie before the runner reaped it.

Runner-owned `wait4` reports lifetime maximum RSS **126,220 KiB**, covering fork/launcher/payload, not a Lean-only peak. Sampled maxima are **8,130,560 bytes RSS** and **35,553,280 bytes VM**. These sparse samples mainly cover the launcher and cannot identify the failed Lean process's actual maximum virtual address demand. No continuous VM-peak claim is made.

The direct child was reaped, existing fail-stop lifecycle cleanup completed, and kernel ECHILD was verified. All descendants were gone. The same universal lock, device **33**, inode **3849**, was held through preservation checks and finalization and was subsequently observed free. Terminal inspection found no compiler/checker/extractor.

## Finite preflight and required preservation phases

Each authorized hash phase recorded **66,977** input rows and **54,367** successful eligible-file advice calls over **6,499,759,546 bytes**, with zero advice errors. **12,610** rows were excluded from advice by the allowlist. These were the planned preflight inventory pass and post-run preservation verification, not extra cache-only experiments or retries. Successful advice returns do not assert reclaimed bytes.

The before/after input inventories are byte-identical, SHA256 **`70f18a7c8847f2458c9c3f49122e8c7739860754bc6cb651ff5fa388adcb6625`**. All prior input identities/hashes remained unchanged. Full inventories, raw advice logs, samples, raw fatal diagnostic, receipt and submitted source are preserved. [386 ordered chunks](chunks/manifest.json) reconstruct both input inventories and both advice logs; concatenation hashes were verified.

No cache deletion, forced sync, global cache drop, download, extraction, fallback, cap increase, source/correctness change, clean-gate change, installation or CI dispatch occurred. All old tracked files/evidence remain unchanged. The new fixed paths remain preserved to prevent automatic reuse.

This attempt does **not** establish bounded import loading, proof replay, a full clean build, heavier-module capacity, cache authentication, CI readiness or whole-paper completion. Publish additively with CI skipped and stop for independent review.
