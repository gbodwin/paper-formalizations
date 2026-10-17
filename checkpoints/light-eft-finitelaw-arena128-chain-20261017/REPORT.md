# Arena128 FiniteLaw chain: refused before child creation

**ADMISSION_REFUSED; ZERO LEAN CHILDREN.** The single authorized fresh chain invocation stopped at its post-preflight memory gate. Compilation, official resolution and singleton kernel replay did not run. The new allocator setting was **not exercised**. There is no new allocator-reservation log, parsed runtime arena value, child-side errno, proof result or output object.

## Actual gate result

Attempt `6bbf43285da54a99887435b9a4124d5e`, created 2026-10-17T14:35:10.593004+00:00, finalized 2026-10-17T14:36:12.804903+00:00. Child PID and exit code are null, because no child was spawned.

| Post-preflight observation | Bytes |
| --- | ---: |
| Required visible headroom | 3,758,096,384 |
| Actual visible headroom | 3,597,119,488 |
| Shortfall | 160,976,896 |
| Host MemAvailable | 17,668,153,344 |

The parent visible cgroup limit was 17,179,869,184 bytes and current usage 13,582,749,696 bytes. Host MemAvailable passed; visible headroom failed. [Authoritative receipt](evidence/compile/receipt.json) records `RuntimeError('Visible headroom below required floor')`. [Supervisor diagnostic](invocation.log) preserves the traceback. This is a supervisor admission refusal, not a compiler error or warning. There is no raw child log because no child existed.

No retry, resource reclamation experiment, redownload, cap increase or gate relaxation followed. Hidden ancestor limits remain unknown under the existing reviewed partial-visible accounting rule.

## Exact prepared change, not executed

The prior bounded chain is preserved at evidence `5ffa5b72db912bfa251a07c9aacb42a67a47464e`. [approved-changes.diff](approved-changes.diff) records only fresh fixed paths, explicit `MIMALLOC_ARENA_RESERVE=128MiB` in every stage, `MIMALLOC_VERBOSE=1` for compilation only, and a post-success compile-log check requiring exactly `arena_reserve: 131072 KiB` before continuing. The code records reservation lines. Resolver/replay omit verbosity so their exact checks remain applicable. No bare numeric allocator unit was used.

Fresh root suffix: `a40ab521630c483a93239651b198d246`. The output root began empty and remains empty. Planned compilation command, recorded but never spawned:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-a40ab521630c483a93239651b198d246/objects/LightEFTSpanners/FiniteLaw.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

All existing limits and safeguards remain unchanged: planned child AS soft/hard 3,221,225,472 bytes, CPU 60 seconds, wall 90 seconds, FSIZE 16 MiB, CORE 0, 512 MiB stop floor, fresh visible/host 3.5 GiB admission before each child, kernel limit readback before exec, OOM/PID monitoring, hash/advice, common exclusion lock and fail-stop cleanup. **No child limit handshake occurred**, so these are configured limits, not newly observed child limits.

The existing official-resolution harness and singleton checker command remain prepared but unrun. Checker would use only `leanchecker -v LightEFTSpanners.FiniteLaw`, with explicit LEAN_NUM_THREADS=1 and LEAN_STACK_SIZE_KB=65536, no compiler-only flags and no aggregate-prefix replay. Six harmless in-process environment/argv/parser checks passed. The same model was retained.

## Source, dependencies and interpretation

Frozen production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`. The actual FiniteLaw source is unchanged and byte-compared to that commit, SHA256 `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`. Official compiler hash `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; official checker hash `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`. Source, executables, harness and unchanged dependency inputs are bound by the preserved inventories. Project object search paths contain only the fresh output root before dependency/toolchain roots.

The reviewer's malloc/read fallback explanation motivated the approved setting. This refused invocation supplies no new evidence for or against that explanation, permission denial, missing files, allocation failure or a unique cause of the prior compiler read error. The instruction to obtain child-side errno if the same failure recurs remains outstanding; that compiler failure did not recur here because no child ran. No further configuration change was made.

This remains a bounded route using existing dependency objects, not a full clean gate. Archive authentication remains incomplete. No successful project compilation, object resolution, kernel replay, CI readiness or whole-paper completion is claimed.

## Preservation and terminal state

All 66981 input rows were verified before and after; inventories are byte-identical, SHA256 `f989612b50b0cbad526b589115b6c2958219b52cbe460db9648fa66d5dec6996`. [386 ordered chunks](chunks/manifest.json) reconstruct the full input/advice records, with originals retained. All prior sources, pins, partial proofs, failed attempts and evidence remain unchanged.

Before/after same-UID threads: 245; both visible pids.current: 267; pids.events max 0 unchanged. Parent OOM/kill/group counters stayed 1/1/0 and child-group counters 0/1/0. Full PID/memory observations are preserved. No child needed reaping; the kernel no-children check passed. Input preservation passed. The common lock device 33/inode 3849 is free, and no Lean/Lake/checker/extractor is active. The fresh directories and single-use invocation marker are consumed and preserved. Existing scripts/__pycache__ remains untouched.

Publish this refusal evidence with CI skipped, then stop. No retry is authorized by this report.
