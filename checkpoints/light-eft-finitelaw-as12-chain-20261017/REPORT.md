# Untraced FiniteLaw chain: immediate external RSS stop during compilation

**COMPILE_SIGKILL_BY_OWNED_GROUP_RSS_GUARD; RESOLUTION_AND_REPLAY_NOT_STARTED.** One fresh untraced compilation ran with independently verified 12 GiB AS limits. The external monitor observed RSS reaching its 2 GiB stop threshold, immediately sent SIGKILL to the owned group before persistence, and reaped the child with exit -9. No output object was produced. The chain stopped at that first failure; no resolver, checker, retry or post-attempt configuration change occurred.

## Preserved raw trace publication repaired before execution

The accepted 96,504-byte raw failed-syscall trace was absent from commit `472efe12a52cbec294bff6d9dec3ed14b37641c3` because `.gitignore` excluded `*.trace`. Its local bytes were intact and matched the accepted manifest. The exact existing file was force-added without changing any ignore rule and published **before this chain** at `c3e356afbc8aa38d57fa4849515155d88f84a6a1`.

[Published original raw trace](https://github.com/gbodwin/paper-formalizations/blob/c3e356afbc8aa38d57fa4849515155d88f84a6a1/checkpoints/light-eft-finitelaw-failed-syscalls-20261017/evidence/compile/syscalls.trace): SHA256 **`bdfea71a593885b885c87857c38db7f8bb5cdb364caf83df7aefa5c67cfbb37b`**, Git blob `ec21b34ec703b6a638fbc9369da8bde62b650cb4`. GitHub-fetched remote bytes were independently decoded and matched the recorded byte count and SHA256. [Repair record](trace-publication-repair.json) preserves the match and publication identity. No trace was rerun. An initial oversized checksum command was rejected before process creation; the remote digest was then checked in-process, with standard SHA256 vectors, and that transport failure is retained in the repair record.

## Frozen source and actual compilation

Production source commit: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. FiniteLaw was byte-compared with that commit and remains unchanged, SHA256 `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`. Official unmodified Lean 4.34.0 executable SHA256 remains `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. All existing source pins and dependency input coverage were retained.

Attempt `5690e40775f748668b8a10bdfb9bb237`, supervisor PID 157980, actual Lean PID 158019; created 2026-10-17T16:13:20.256634+00:00, finalized 2026-10-17T16:14:32.592183+00:00. These times include preflight and preservation hashing. The child's wall bound alone was 90 seconds.

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M1536 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-ee73db0a907a4ca0b183ed0fcd5c95c6/objects/LightEFTSpanners/FiniteLaw.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

The project output root was freshly created and initially empty, and was the only project-object search root. No inherited project objects were used. [The receipt](evidence/compile/receipt.json) binds source, executable, environment, input hashes, actual PID/session/group/lock and kernel readbacks. [Raw output](evidence/compile/raw.log) contains mimalloc initialization and the expected arena_reserve 131072 KiB / reserved 131072 KiB lines. No compiler error or warning was printed before interruption. Allocator option names such as max_warnings do not count as warnings. This interruption is not a theorem failure or successful compilation.

## Memory policy, actual stop and evidence limits

Actual pre-exec kernel soft/hard limits: AS **12,884,901,888 bytes**, CPU 60 seconds, FSIZE 16 MiB, CORE 0. The larger AS budget permits virtual file mappings; it is **not a 12 GiB RAM allowance**. Compiler and planned resolver use -j1 -s65536 -M1536 with existing strict proof flags and MIMALLOC_ARENA_RESERVE=128MiB. `-M1536` is an intermittent runtime RSS check, not a kernel heap or hard RSS cap. The external policy remained necessary.

The external monitor samples every 250 ms and stops on:

- observed live RSS at least **2,147,483,648 bytes**;
- visible cgroup headroom or host MemAvailable below **1,073,741,824 bytes**;
- missing live RSS/VM information or untrustworthy memory accounting.

A memory breach signals the owned group with SIGKILL immediately, before any diagnostic persistence, followed by the existing fail-stop cleanup. The actual stop reason was `Observed live RSS reached 2 GiB stop`; the signal was sent to group 158019 and the child exited -9. No cgroup OOM counter changed, so this must not be described as a kernel OOM kill.

[Resource-stop summary](resource-stop-summary.json) records dispatch timestamps and qualification. The signal-call markers span 39,397 ns; these measure the local dispatch interval, not detection latency from the beginning of growth. The last accepted logged sample preceded signal dispatch by 251,298,233 ns.

| Measurement | Bytes |
| --- | ---: |
| External RSS stop threshold | 2,147,483,648 |
| Kernel wait4 lifetime RSS high-water | 2,313,826,304 |
| High-water above threshold | 166,342,656 |
| Last accepted logged RSS peak | 1,342,881,792 |
| Last accepted logged VM peak | 5,360,865,280 |

The wait4 high-water is 2,259,596 KiB across the same launcher/Lean PID lifetime. The guard checks before returning a sample to the logger, so the exact triggering RSS/VM sample was **not appended**; its values cannot be reconstructed from the logged sampled peaks. Only the threshold crossing and kernel high-water are established. The table's logged peaks are prior accepted samples, not lifetime maxima. This is a preserved instrumentation limitation, not a reason to change or rerun the attempt.

Sampling allows overshoot between polls. The process did not remain below 2 GiB at all times; the observed high-water is about 166 MB above the threshold. Neither the external monitor nor -M1536 is a kernel physical-memory cap. This result establishes correct observed-stop behavior and cleanup, not adequate memory capacity for FiniteLaw.

## Harmless tests and unchanged sequencing

[Memory guard tests](harmless-tests.json) check exact thresholds, missing-live-RSS rejection, zombie-state handling, supported checker environment and the new AS budget. Four harmless sleeping Python child groups were launched sequentially under the common lock, with synthetic visible/host/RSS/missing-RSS failures. Each fixture received real SIGKILL before the persistence callback, exited -9, and was reaped; UUID fixture receipts are preserved. No Lean/checker/tracer ran in these tests.

[approved-changes.diff](approved-changes.diff) records reuse of the untraced supervisor, streamed completed-file housekeeping, 12 GiB AS/M1536, visible+host 1 GiB ongoing floors, the RSS stop, missing-live-RSS handling and immediate group kill. The existing actual-PID/limit/lock checks and fail-stop cleanup were retained. Fresh visible and host admission/pre-exec gates stayed **3,758,096,384 bytes**:

| Gate | Visible headroom | Host MemAvailable |
| --- | ---: | ---: |
| Admission | 3,973,107,712 | 17,808,797,696 |
| Pre-exec | 3,968,831,488 | 17,808,723,968 |

The prepared chain continues only on successful compile, then exact official target/object resolution, then one singleton official leanchecker replay with LEAN_NUM_THREADS=1 and LEAN_STACK_SIZE_KB=65536. Checker argv contains no compiler -j/-s/-M flags. Because compile stopped, **both later stages were unrun**; there is no new object hash, resolution or replay result.

## Exact cache pass and preservation

After the single full preflight, the fixed [history whitelist](history-whitelist.json) advised exactly **407 files / 183,081,165 bytes**, derived from the raw reconstruction files and chunks in `472efe12a52cbec294bff6d9dec3ed14b37641c3`'s manifest. All published hashes and same-descriptor identities matched. There was no recursive expansion or retry loop. Visible usage decreased by 185,917,440 bytes around the one pass; measured changes are not exclusive causal attribution. Own completed files were streamed/flushed/fsynced, hashed and advised, with before inventory retained and no repeated preflight before launch.

All 66983 configured input rows verified before and after. The inventory files are byte-identical, SHA256 `0ebf906836c3c046c6029d7932b89f17d55a415fde066a402bad119f36efaf14`. [388 ordered chunks](chunks/manifest.json) reconstruct the raw inventories and advice logs. Raw monitor data, source snapshot, kernel-limit handshake, guard event and all failed outcomes are preserved. No partial output files existed to copy. Packaging occurred only after child cleanup.

Before/after same-UID threads stayed 261 and visible pids.current 283; pids.events max 0 unchanged. Parent OOM/kill/group counters remained 1/1/0; child-group 0/1/0. All descendants were gone, direct child reaped and kernel ECHILD verified before lock release. The universal lock device 33/inode 3849 is free and no Lean/Lake/checker/extractor/tracer is active. Existing scripts/__pycache__ remains untouched.

All prior proof source, partials, failed attempts and evidence remain preserved. Existing incomplete dependency-archive authentication and partial visible-ancestor accounting qualifications remain. This is a single-module bounded-route resource stop, not proof acceptance, full-clean validation, CI readiness or whole-paper completion. Publish with CI skipped and stop for independent review.
