# One revised 64 MiB-thread-stack import: child failed

**STACK64_CHILD_FAILURE_SIGABRT_NO_IMPORT_SUCCESS.** One authorized `run_once()` invocation and one Lean child, with no retry or cap increase. UUID **`34e112168e9944888c7fbc78040eef32`**, child PID **152148**. Attempt created **2026-10-17 13:56:45.301480 UTC**, finalized **13:57:47.962816 UTC**.

## Exact authorized change

The preserved hash-then-advise runner from result commit `afe8f90fbe300f3eb34abd492b7c2f72ae061022` was copied byte-for-byte except for two fresh fixed paths (suffix `39f7aa87c8354cebbf81f9df940eccd2`) and insertion of **`-s65536`** in both exact argv and its allowlist. [approved-change.diff](approved-change.diff) records those changes. The launcher, accounting and advice helpers are unchanged. All consumed paths and prior runners remain preserved. Frozen production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`.

Command:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true /workspace/light-eft-verification/.lake/bounded-import-20261017-39f7aa87c8354cebbf81f9df940eccd2/ImportSmoke.lean
```

Source remains only `import Aesop.Script.Tactic`. The official executable hash, dependency-only search paths, environment allowlist, AS/CPU/wall/memory gates, per-file hash/advice and preservation checks remain unchanged. No object-output option was added.

The independently supplied diagnosis suggested that large default Lean thread virtual-stack reservations might conflict with the 1.5 GiB AS cap, and approved the official `-s65536` option (64 MiB stack setting, with runtime overhead). `-j1` is a taskpool setting, not a claim of one OS thread. That reservation explanation was a hypothesis, not an established cause. This revised attempt still failed and neither establishes the cause nor rules out all address-space/thread constraints.

## PID and inherited-limit observations

`invoke_once.py` captures pre/post observations under the same exclusion lock and refuses before `run_once` if observed PID/NPROC limits are exhausted or another compiler is active. A one-use marker prevents reuse of this invocation wrapper. Full data: [before](pid-limits-before.json), [after](pid-limits-after.json).

| Observation | Before | After |
| --- | --- | --- |
| RLIMIT_NPROC soft/hard | 71,955 / 71,955 | unchanged |
| RLIMIT_STACK soft/hard | 8,388,608 bytes / unlimited | unchanged |
| Observed same-real-UID threads | 235 | 235 |
| Parent pids.current / max | 257 / max | 257 / max |
| Child-group pids.current / max | 257 / max | 257 / max |
| Parent/child pids.events | max 0 / max 0 | unchanged |
| Active compiler/checker/extractor | none | none |

These observations did not show exhausted PID/thread limits. Hidden ancestor PID limits remain unknown; `max` in the visible groups is not a global unlimited assertion. The inherited RLIMIT_STACK observation is separate from the explicit Lean worker-stack CLI setting. No process/thread limit or security setting was changed.

## Admission, handshake and failure

After the single finite preflight hash/advice phase, memory admission passed: visible parent limit **17,179,869,184 bytes**, current **12,417,699,840 bytes**, headroom **4,762,169,344 bytes**, exceeding the unchanged **2 GiB** gate. The supervisor verified the pre-exec handshake and kernel soft=hard child limits: AS **1,610,612,736**, CPU **60 seconds**, FSIZE **16,777,216**, CORE **0**. The 90-second wall deadline and 512 MiB stop floor remained unchanged.

The sole fatal diagnostic was:

```text
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable
```

The child exited **-6 (SIGABRT)**; the wrapper exited 1. This is a runtime failure with undetermined precise cause, not a proof failure or import success. There was no fallback, environment workaround, additional cache-only pass, cap increase or automatic retry.

Runner-owned wait4 reports lifetime maximum RSS **126,712 KiB**, including fork/launcher/payload. Sparse sampled maxima were **8,130,560 bytes RSS** and **35,553,280 bytes VM**; these cannot establish the failed payload's actual maximum virtual-address demand or explain thread failure. The raw samples and receipt remain preserved.

## Preservation and cleanup

Each authorized hash phase recorded **66,977** input rows and **54,367** successful eligible advice calls over **6,499,759,546 bytes**, with zero advice errors. These were the specified preflight and post-run preservation phases, not repeated experiments. Before/after input inventories are byte-identical, SHA256 **`270ffbc27e5fcd67405e3b8f619c500882e7f34407fc3e891c65220c7830da57`**. All prior tracked sources/evidence remain unchanged.

The direct child was reaped, all descendants were gone and kernel ECHILD was verified. The same universal lock (device **33**, inode **3849**) was held through cleanup/preservation and was subsequently observed free. No compiler/checker/extractor remains active. The two new one-attempt directories and wrapper marker are consumed and preserved; no reuse was attempted.

Full receipts, fatal output, source, inventories and advice logs are retained. [386 ordered chunks](chunks/manifest.json) reconstruct the large records; concatenation hashes were verified. No download, extraction, deletion, clean-gate change, installation or CI dispatch occurred.

This failed revised attempt establishes no bounded import loading, proof replay, full clean build, heavier-module capacity, archive authentication, CI readiness or mathematical completion. Publish with CI skipped and stop for independent review.
