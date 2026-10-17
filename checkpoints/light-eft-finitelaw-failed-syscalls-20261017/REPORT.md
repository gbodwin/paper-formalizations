# FiniteLaw diagnostic captures ENOMEM followed by null-buffer EFAULT

**NAMED-FILE_MMAP_ENOMEM_THEN_NULL_READ_EFAULT; LEAN_EXIT_1.** Exactly one fresh diagnostic compilation ran. The actual Lean process and tracer both exited 1; all four observed Lean thread exit records are preserved. The narrowed trace completed at **96,504 bytes**, below its unchanged 16 MiB bound. No object, resolver or checker result was produced. No retry or post-attempt configuration change occurred.

## Exact observed failing sequence

[Raw failed-syscall trace](evidence/compile/syscalls.trace), lines 415–421, worker TID 157480:

```text
mmap(0x635cddb80000, 576104, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_FIXED_NOREPLACE, 10</workspace/paper-formalizations/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/HigherOrder.olean.private>, 0) = -1 ENOMEM
mmap(NULL, 577536, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) = -1 ENOMEM
mmap(NULL, 134217728, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) = -1 ENOMEM
mmap(NULL, 67108864, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) = -1 ENOMEM
mmap(NULL, 577536, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) = -1 ENOMEM
mmap(NULL, 1048576, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) = -1 ENOMEM
read(0xa, 0, 0x8ca68) = -1 EFAULT
```

The raw file retains original thread IDs, timestamps, durations, errno descriptions and descriptor paths. fd `0xa` is decimal 10; requested read size `0x8ca68` is **576,104 bytes**, matching the named private file. The read buffer address is **zero**. [Compiler output](evidence/compile/raw.log) reports the same `failed to read file ... HigherOrder.olean.private` error.

The trace contains **418 mmap ENOMEM failures**, **one read EFAULT**, and **two lseek ESPIPE** results. It has no partial final line and did not hit the trace bound. [Concise errno/maps summary](diagnostic-summary.json) preserves the critical source-line references, exit records, counts and sampling limitations. No duplicate full decoded mapping collection was generated.

This directly establishes allocation/mapping failures and a subsequent null-buffer read in this constrained run. The named descriptor path and matching worker/fd/size sequence strongly support the allocation-failure/null-buffer fallback mechanism behind the compiler's unsuffixed read error. The sampled VM reached the enforced **3,221,225,472-byte AS cap** while sampled Lean RSS was about 195 MiB, with no new cgroup OOM event. Address-space pressure is therefore supported by actual kernel errno, not inferred from the text “failed to read file” alone. It is not a proof of every prior untraced failure or behavior without these resource constraints.

The selected filter excludes successful calls and all open/stat calls. It does **not** directly record successful open/header reads, positive short reads, or brk requests returning the old break without an errno. Absence of another call is not proof that it did not occur. The syscall summary cannot reconstruct the entire virtual-memory budget. No broad permission-denial, missing-file, corruption or unique-cause assertion is made.

The input file is preserved in the before/after inventories: 576,104 bytes, SHA256 `1dd5e6457e93a4a7c870e8d34dd5f79e5d72cd6a478115b7dd1f972ea77053a9`. No file was redownloaded, replaced or modified.

## Frozen source and actual identities

Production source commit: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. FiniteLaw is unchanged and was compared byte-for-byte with that commit, SHA256 `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`. Official Lean 4.34.0 compiler SHA256 remains `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; the previously reviewed strace 6.13+ds-1 executable remains SHA256 `69f88291a4e47f258b8e32b089c919a247509f063ef3d6afe5389939051102b3`. No capability probe or installation was repeated.

Attempt `ef2daf29f98b41459f0590835f79a6a0`, supervisor PID 157435, tracer PID 157474, actual Lean PID 157477. Created 2026-10-17T15:53:25.665457+00:00, finalized 2026-10-17T15:54:29.704523+00:00, including preflight and preservation. The [receipt](evidence/compile/receipt.json) binds exact source/executable/dependency hashes, actual Lean PID/TracerPid/parent/session/lock checks and kernel readbacks.

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-4ba0428af86f49edab8807443909f413/objects/LightEFTSpanners/FiniteLaw.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

The project output root was initially empty and was the only project-object search root. No object was produced. The compiler emitted one input-loading error and zero reported compiler warnings. Mimalloc option/statistics lines, including max_warnings, are not compiler warnings. The existing allocator setting remains explicit `MIMALLOC_ARENA_RESERVE=128MiB`; compilation-only verbosity confirms arena_reserve 131072 KiB and a 131072 KiB reservation. All source, model and other compiler flags remain unchanged.

## Narrow filter, actual caps and map coverage

[approved-changes.diff](approved-changes.diff) records the reviewed changes from the prior partial trace: fresh paths/whitelist, `status=failed`, restriction to mmap/mremap/mprotect/munmap/brk/lseek/read/pread/readv families, 64 MiB tracer postfork AS, the corrected pair gate, and near-cap map selection. `-f`, thread IDs, timestamps, durations, descriptor decoding and raw address-only read rendering were retained. The trace has zero read-buffer string dumps. Eight existing harmless mocked contract checks passed; no new tracing framework or repeated capability probe was introduced.

Actual kernel readbacks before Lean exec:

- Lean AS soft/hard **3,221,225,472 bytes**, CPU 60 seconds, FSIZE 16 MiB, CORE 0.
- Tracer bootstrap AS 3 GiB, reduced after tracee fork to soft/hard **67,108,864 bytes**, independently read back before Lean exec. Its CPU/FSIZE/CORE caps remained unchanged.
- Pair wall bound 90 seconds, ongoing headroom stop floor 512 MiB, trace bound 16 MiB and raw map-sample bound 4 MiB.

The 250 ms sampled peaks were tracer RSS 2,420,736 bytes / VM 5,885,952; actual Lean RSS 204,763,136 / VM 3,221,225,472; combined RSS 207,183,872. wait4 maximum RSS was 199720 KiB across the tracer/launcher tree lifetime, not a Lean-only measurement. Sampling is not continuous.

Raw map snapshots were reserved for the approved actual PID after its executable matched pinned Lean and sampled VM was at least **2,952,790,016 bytes** (within 256 MiB of the AS cap). Three raw snapshots were retained, without a second decoded collection. The first two hit the existing 1 MiB per-snapshot read bound and are truncated lower bounds; their summed parsed regions are not full process VM. The third raced with process exit, omits the Lean executable, and cannot represent peak VM. The concise summary records those qualifications. The executable/VM guard before reading does not make a /proc read atomic.

A metadata-generation IndexError occurred before any child was started, from reusing a temporary preparation variable while writing PLAN.json. It was corrected before the one diagnostic invocation; [the preparation diagnostic](preparation-diagnostic.txt) is preserved. No compiler/tracer attempt was retried.

## One hot-history pass, fresh gates and preservation

The exact [whitelist](history-whitelist.json), SHA256 `a628d5dc327a905e735ab4a0f042f87453a2e0e892e73936c896b4049e4939d5`, was derived from raw reconstruction files and chunks in the published partial-trace manifest at `fbdb58f44adbb9447864c27a9415e9dd7c880832`. It contains **504 distinct files / 222,716,878 bytes**. After the single full preflight, one fixed same-descriptor hash/identity/advice pass verified every published hash and preserved all files. No recursive expansion occurred. Visible usage decreased by **226,541,568 bytes** around that pass; this is measured accounting, not exclusive causal attribution.

Own completed inventories/logs were streamed, flushed/fsynced, same-descriptor hashed/identity-checked and advised before measurement. The before inventory remained for preservation. No second preflight or bulky publication intervened before launch. Pair admission and pre-exec required **3,825,205,248 bytes**, equal to Lean 3 GiB + tracer 64 MiB + 512 MiB margin:

| Gate | Visible headroom | Host MemAvailable |
| --- | ---: | ---: |
| Admission | 4,001,828,864 | 17,793,462,272 |
| Pre-exec | 3,996,495,872 | 17,792,843,776 |

All 66985 source/executable/dependency rows verified before and after. Inventory files are byte-identical, SHA256 `fc4fc1f448c03e3b62e0e954a6246d4fc53146b234e217846c579c7bdefd18aa`; nine completed-file housekeeping records reconcile. [401 ordered raw reconstruction chunks](chunks/manifest.json) cover the necessary verification inventories/logs and raw map samples. The 96,504-byte syscall trace is preserved once as a directly readable raw file, with a concise summary. No duplicate large decoded trace/mapping collection or readable-map copy was created. Packaging occurred only after execution ended.

## Terminal state and bounded conclusion

The tracer was directly reaped. Raw trace exit records show actual Lean PID 157477 and its three observed thread IDs exiting 1; there was no trace-bound termination or forced cleanup signal. All descendants were gone and kernel ECHILD verified before common lock release. Input preservation passed. No resolver/checker, retry, cap increase or post-attempt configuration change occurred. The common lock device 33/inode 3849 is free and no compiler/tracer remains active. Existing scripts/__pycache__ was left untouched.

All prior sources, proofs, partials, failed attempts and evidence are preserved. Dependency archive authentication and hidden-ancestor accounting qualifications remain unchanged. This checkpoint supplies actual constrained-process ENOMEM/EFAULT evidence; it establishes no successful proof compilation, kernel acceptance, full-clean validation, CI readiness or whole-paper completion. Publish with CI skipped and stop for independent review.
