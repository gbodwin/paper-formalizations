# Tracing permitted; FiniteLaw diagnostic refused before process creation

**DIAGNOSTIC_ADMISSION_REFUSED; ZERO DIAGNOSTIC TRACERS OR LEAN CHILDREN.** The installed tracer and harmless capability probe passed, but the single fresh diagnostic invocation failed the unchanged visible-headroom gate. No compile trace, mapping trace for Lean, new child-side errno, output object, resolver or checker execution exists. No retry or configuration adjustment followed.

## Capability actually established

[Installed tracer and harmless probe evidence](../light-eft-strace-capability-20261017/REPORT.md) binds `/usr/bin/strace` 6.13+ds-1, SHA256 `69f88291a4e47f258b8e32b089c919a247509f063ef3d6afe5389939051102b3`. It matches installed package metadata. The package-wide check's missing documentation/man files were preserved and distinguished from executable integrity. No installation/security/permission change or denial bypass occurred.

Exactly one ordinary own-child capability probe, tracing `/usr/bin/true`, exited zero. It preserved successful mappings and address-only reads in its 1,986-byte trace. The probe tracer and harmless child finished, descendants were gone and kernel ECHILD verified before lock release. This demonstrates current tracing permission; it does not supply Lean syscall evidence.

## Actual diagnostic admission refusal

Attempt `7bf0063fbeb149b4a078f0c0e2dedff5`, created 2026-10-17T15:12:47.051948+00:00, finalized 2026-10-17T15:13:51.659087+00:00. Tracer PID, actual Lean PID and exit code are null: the diagnostic spawned neither process.

| Fresh post-preflight/history gate | Bytes |
| --- | ---: |
| Required visible headroom and host MemAvailable | 3,758,096,384 |
| Actual visible headroom | 3,745,497,088 |
| Visible shortfall | 12,599,296 |
| Host MemAvailable | 17,807,069,184 |

Host MemAvailable passed; visible headroom failed. [Authoritative receipt](evidence/compile/receipt.json) and [supervisor traceback](invocation.log) retain `RuntimeError('Visible headroom below required floor')`. This is admission refusal, not a compiler diagnostic. It does not show ptrace denial. No tool approval was needed.

The preflight ran once and retained the full before inventory. New inventories/advice logs were streamed, flushed, fsynced, same-descriptor hashed/identity-checked and advised. The existing fixed history pass ran exactly once: **1,560 files / 710,100,227 bytes**, all published hashes/identities verified, with no recursive expansion. It used the unchanged four-manifest whitelist from the accepted integrated-housekeeping route. History-pass visible current usage increased by 114,688 bytes rather than decreasing; successful advice does not establish new reclamation. The gate was measured afterward under the same lock. No bulky packaging preceded admission.

## Prepared diagnostic support, not exercised

[base-changes.diff](base-changes.diff), trace_supervisor.py, and chain.py preserve the prepared one-compile design. Frozen source remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`; unchanged FiniteLaw source SHA256 `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`. It was byte-compared to that commit before the attempted diagnostic. The official compiler hash remains `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.

The unexecuted compiler argv remains:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-94757f2e1a12440b91b7674e10b909a5/objects/LightEFTSpanners/FiniteLaw.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

Actual Lean settings would remain AS soft/hard 3 GiB, -j1 -s65536 -M512, strict warning flags, MIMALLOC_ARENA_RESERVE=128MiB and compilation verbosity. CPU 60 seconds, wall 90 seconds, FSIZE 16 MiB, CORE 0 and monitored stop floor 512 MiB are unchanged. Since no process was spawned, no new actual-PID kernel limit readback occurred.

The prepared tracer follows threads and records open/stat, all successful and failed mmap/munmap/mprotect/brk, lseek, reads and closes with errno/descriptor paths. The read/pread/readv families use raw address rendering, not file-content dumps. Trace output is bounded to 16 MiB; optional ordinary map samples to 4 MiB. The launcher isolates the actual Lean process group, verifies its real PID/parent/TracerPid, inherited common lock and kernel limits before exec. The tracer initially inherits the existing 3 GiB bootstrap cap, then its own AS is reduced and independently checked at 256 MiB after the tracee fork and before Lean exec. Tracer/tracee RSS/VM would be sampled separately and together. The existing fail-stop barrier would reap the direct tracer and any adopted tracee before lock release. **These production-pair checks were not exercised**, because admission refused first.

Eight harmless in-process mocked identity/limit/lock and command-contract checks passed. They establish preparation checks only. No extra tracer or compiler was started by those tests. The only executed tracer was the single harmless capability probe.

## Preservation and terminal state

All 66985 input rows remain unchanged; before/after inventories are byte-identical, SHA256 `212b49b8e7bdc383db2904a0682d93d3aec857fb23c9135f6fb49b21ba9794cc`. All five completed new-file housekeeping records reconcile to preserved hashes and identities. [392 ordered chunks](chunks/manifest.json) reconstruct the full inventories, advice logs and history log. Raw originals, failed preparation metadata, refusal diagnostics, before/after PID/OOM observations and focused checks are retained. No partial output object exists.

Kernel ECHILD and input preservation passed. The common lock device 33/inode 3849 is free, and no Lean/Lake/checker/extractor/tracer remains active. The one-use markers and fresh directories are consumed. No prior source, dependency pin, proof, partial result or evidence was changed. Existing scripts/__pycache__ remains untouched.

The prior accepted failure remains the last actual Lean result: HigherOrder.olean.private read failure with sampled VM at the 3 GiB cap. **Its child-side errno remains unresolved.** This refusal adds no evidence for ENOMEM, EFAULT, permissions or any unique cause. No additional tracing attempt or configuration change was made.

Existing dependency archive authentication and hidden-ancestor accounting qualifications remain. No proof acceptance, full-clean validation, CI readiness or whole-paper completion claim. Publish with CI skipped and stop.

## Publication blocker

The evidence commits were created locally, but the authorized push failed because Git could not read a GitHub username (`No such device or address`). The exact failure is preserved in publication-push-failure.txt. No credentials were added or changed and the push was not retried. The remote branch was observed still at `9db69c4fc1717d5551d06fc40a34d4c76a2229da`; this diagnostic checkpoint is local only.
