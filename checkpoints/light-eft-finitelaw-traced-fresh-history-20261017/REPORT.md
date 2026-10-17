# Traced FiniteLaw diagnostic: trace file bound reached, pair cleaned up

**PARTIAL_TRACE_ONLY; TRACER_SIGXFSZ; LEAN_TERMINATED_DURING_FAIL_STOP_CLEANUP.** One fresh traced compilation was authorized and attempted. Both admission gates and actual-PID kernel limit checks passed. The 16 MiB trace bound was reached; the tracer exited with SIGXFSZ (-25), the Lean child was adopted by the supervisor, and the parent-change guard stopped the attempt. Cleanup reaped the adopted Lean child with wait status 15 (SIGTERM). No normal compiler completion, output object, resolver or checker result is established. No retry or configuration adjustment followed.

## Exact source, identities and command

Frozen production source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. FiniteLaw was byte-compared to that commit and left unchanged, SHA256 `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`. The official Lean 4.34.0 executable remains SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. The already reviewed strace 6.13+ds-1 executable remains SHA256 `69f88291a4e47f258b8e32b089c919a247509f063ef3d6afe5389939051102b3`. No capability probe was repeated and no tool was installed.

Attempt `593636806ad040e5ad821adbf533b720`. Supervisor PID 156926; tracer PID 156965; actual Lean PID 156968. Receipt created 2026-10-17T15:36:18.267696+00:00, finalized 2026-10-17T15:37:23.542704+00:00; these times include pre/post verification.

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-e646f8ac36b6457cb452ce4671ad611b/objects/LightEFTSpanners/FiniteLaw.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

The output root was fresh and initially empty. Only that root preceded dependency/toolchain roots as a project-object search path. [The receipt](evidence/compile/receipt.json) preserves exact compiler/tracer argv, explicit environment, source hash, executable/dependency inventories, actual parent/TracerPid/session/lock handshake, kernel readbacks and sampled role-separated resources. The [trace analysis](trace-analysis.json) preserves both actual execve records and observed Lean thread IDs 156968–156971. No aggregate-prefix replay was prepared for execution.

MIMALLOC_ARENA_RESERVE=128MiB and compilation-only MIMALLOC_VERBOSE=1 were unchanged. [Raw output](evidence/compile/raw.log) confirms `arena_reserve: 131072 KiB` and `reserved 131072 KiB memory`. There is no captured Lean error or warning; option/statistics lines are informational and must not be counted as warnings. Compiler completion was interrupted, so absence of a diagnostic is not acceptance.

## What the partial syscall evidence establishes

[Original trace](evidence/compile/syscalls.trace): exactly **16,777,216 bytes**, SHA256 `36289c2a038f375119162fe213344e4afb8654f62cbaefed59808e80b2302999`. Its final statx line is truncated mid-record. The tracer's direct wait4 status is -25; this must not be reported as Lean's own exit code. The guard receipt records `RuntimeError('Actual tracee identity/parent changed')`; cleanup shows that same Lean PID adopted by supervisor and reaped with SIGTERM, not a normal theorem/compiler result.

The captured completed calls include:

| Call | Count |
| --- | ---: |
| mmap | 3,788 |
| mprotect | 25 |
| munmap | 8 |
| statx | 29,152 |
| openat | 3,800 |
| read + pread64 | 3,788 |
| clone3 | 3 |

A further statx call start is the truncated tail. The added mremap filter was active; no mremap call was observed before truncation. Raw address rendering covers read/pread/readv families; offline checks found **zero read-buffer strings**. File descriptors/paths, thread IDs, errno and successful mapping records remain present. No file-content dump was enabled.

Captured errnos are **26,271 ENOENT** path probes and **2 ESPIPE** results. No captured mmap/mremap/mprotect/brk failure, ENOMEM or EFAULT occurs in this partial trace. No trace record names HigherOrder.olean.private or Term.olean.private. Consequently the requested failing-file open/header/mmap/fallback-read errno sequence was **not obtained**. Ordinary path-search ENOENTs do not establish that the prior named files were missing. The original read failure's errno remains unresolved; no permission, corruption, allocation or unique-cause conclusion follows.

[3,838 decoded mapping records](mapping-records.jsonl) retain source line spans and raw call bodies. One observed post-exec reservation is:

```text
mmap(NULL, 1073745920, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_STACK, -1, 0) = 0x7f122ae16000
```

This directly records a 1 GiB plus one-page MAP_STACK reservation. The post-exec syscall-derived mmap union reaches **2,217,877,504 bytes** in the captured segment. It is a partial lower-bound accounting view: initial exec-created maps and brk are not included in that union, and the trace ends early. No whole-lifetime/exact virtual-budget claim is made. Twelve ordinary /proc maps snapshots are retained in map-samples.jsonl and [readable snapshots](maps-readable/manifest.json), including reconstruction hashes. The largest summed snapshot is 2,151,948,288 bytes. Sampling is not continuous and cannot replace missing syscalls after truncation.

## Reviewed changes and unchanged hard budgets

[approved-changes.diff](approved-changes.diff) records only the fresh root, exact new whitelist and pin, 3.75 GiB traced-pair admission/pre-exec gate, and mremap addition. The reviewed actual Lean PID/TracerPid/kernel-limit/inherited-lock/fail-stop checks were reused. Eight existing harmless in-process contract checks passed; there was no repeated tracing capability probe or new execution framework.

Configured and independently read back before Lean exec:

- Actual Lean AS soft/hard: **3,221,225,472 bytes**, CPU 60 seconds, FSIZE 16 MiB, CORE 0.
- Tracer bootstrap AS: 3 GiB; after its tracee fork, tracer AS soft/hard reduced to **268,435,456 bytes**, with its CPU/FSIZE/CORE limits unchanged and independently read back before Lean exec.
- Traced-pair wall deadline: 90 seconds. Ongoing headroom stop floor: 512 MiB.
- Trace log bound: 16 MiB; optional map-sample bound: 4 MiB.

The observed sampled peaks were tracer RSS 2,490,368 bytes / VM 5,885,952, actual Lean RSS 59,707,392 / VM 2,151,215,104, and combined RSS 62,197,760. These are 250 ms samples, not continuous peaks. wait4 maximum RSS 122172 KiB covers the supervised tracer tree/launcher lifetime and is not Lean-only RSS. No compiler/tracer hard budget was raised.

## Fresh history pass, gates and preservation

The exact whitelist was derived and hash-pinned before execution from the raw reconstruction files and chunks named by:

- integrated-housekeeping at `9db69c4fc1717d5551d06fc40a34d4c76a2229da`;
- traced-refusal at `7dd96151b6dd2b731034f9e527937c0e287145c3`;
- stack64-import at `0e2fc0d91ecd7babe19d560ad92efe61b89dec5c`.

[history-whitelist.json](history-whitelist.json) has **1,184 distinct files / 537,041,913 bytes**, SHA256 `2161ff8054eea225534bbeaa3149a4398b68d114fabd1475698dce8307cb68e5`. It was not recursively expanded. The one pass occurred after full preflight verification, using same-descriptor hash/identity checks and DONTNEED. All hashes and identities reconciled. Visible current decreased by **548,327,424 bytes**, with headroom rising from 3,488,157,696 to 4,036,485,120. These are observed counter changes, not exclusive causal attribution to advice.

Each completed new inventory/log was streamed or incrementally written, flushed/fsynced, same-descriptor hashed/identity-checked and advised. The before inventory was retained for preservation. No second preflight, inventory publication or bulky packaging intervened before launch. Packaging began only after cleanup.

Both visible and host headroom gates required **4,026,531,840 bytes**:

| Gate | Visible headroom | Host MemAvailable |
| --- | ---: | ---: |
| Admission | 4,036,501,504 | 17,803,890,688 |
| Immediately before Lean exec | 4,031,422,464 | 17,800,556,544 |

All 66985 source/executable/dependency input rows verified before and after; inventories are byte-identical, SHA256 `87d0a258167cda3ec7da18f8d6c9a3d434b65343262e9f94fdc2055e00073fb1`. Nine completed-file records reconcile. [495 ordered chunks](chunks/manifest.json) reconstruct the original inventories, advice/history logs, full bounded trace, map samples, mapping records and whitelist. The trace's final partial line is preserved without alteration. There are no output object hashes because no object was produced.

Before/after same-UID threads remained 256 and visible pids.current 278; pids.events max 0 unchanged. Parent OOM/kill/group counters remained 1/1/0; child-group 0/1/0. No OOM/PID limit event changed. Hidden ancestor visibility remains qualified under the reviewed bounded route. Dependency archive authentication is still incomplete.

## Recovery status and terminal state

A platform disconnection was reported at 15:40 UTC. At **15:42:01 UTC**, read-only reconciliation confirmed execution available, both processes already reaped, no compiler/tracer active, common lock inode 3849 free, and the raw trace hash unchanged. Cleanup had finished at **15:37:23 UTC**, before that notification. [Connection reconciliation](connection-reconciliation.json) records that no restart or duplicate occurred; continuation was offline packaging/publication only.

The original source, all prior proofs/partials and evidence remain unchanged. The common lock was held through cleanup, kernel ECHILD and preservation. Actual Lean wait status 15 and tracer SIGXFSZ are both retained; normal compiler completion is not claimed. No resolver, checker, retry, cap change, installation, security change or CI was run. Existing scripts/__pycache__ was left untouched.

Publish this bounded partial-diagnostic checkpoint with CI skipped and stop for independent review. It establishes admission, actual limits, address-only tracing and successful mapping evidence through the trace bound; it does not resolve the original failing read errno, establish proof acceptance, full-clean validation, CI readiness or whole-paper completion.
