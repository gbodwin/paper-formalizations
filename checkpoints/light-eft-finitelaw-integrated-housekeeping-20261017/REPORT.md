# Integrated housekeeping admitted the chain; FiniteLaw compilation failed

**COMPILE_EXIT_1; RESOLUTION_AND_REPLAY_NOT_STARTED.** The fixed 1,560-file history pass succeeded. Fresh admission and independently verified child limits passed. One compiler child ran with the intended 128 MiB arena option, then failed while loading a Mathlib private object. No output object was produced; no retry, later stage, cap increase, security change or CI ran.

Frozen production: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. FiniteLaw source is unchanged, SHA256 `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`. The source was byte-compared with that commit before this attempt. All prior proofs, partials, failed attempts and evidence remain preserved.

## Actual execution and failure

Attempt `67afd5f39b794d30b74da5c997e62618`, PID 155445; created 2026-10-17T14:57:01.319756+00:00, finalized 2026-10-17T14:58:04.609201+00:00, including preflight/history/preservation work.

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-6e2868262cf448e88a575667a3a56cee/objects/LightEFTSpanners/FiniteLaw.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

The project output root was freshly created and initially empty; it was the only project-object search root before package/toolchain roots. Official Lean 4.34.0 executable SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Source, executable, harness and dependency bindings are preserved in the input inventories and [receipt](evidence/compile/receipt.json).

[Raw compiler output](evidence/compile/raw.log) includes:

```text
option 'arena_reserve': 131072 KiB
mimalloc: reserved 131072 KiB memory
/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean:1:0: error: failed to read file '/workspace/paper-formalizations/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/HigherOrder.olean.private'
```

This is one compiler input/object-loading error, zero reported compiler warnings. The allocator option/statistics output is informational; occurrences of words such as max_warnings do not count as warnings. Compilation explicitly used MIMALLOC_ARENA_RESERVE=128MiB and MIMALLOC_VERBOSE=1. The arena option was parsed and the reservation line recorded offline in [allocator-observation.json](allocator-observation.json). The normal chain's post-success parser gate was not reached because the compiler exited 1.

Read-only inspection found the named file present, non-symlinked and supervisor-readable: 576,104 bytes, SHA256 `1dd5e6457e93a4a7c870e8d34dd5f79e5d72cd6a478115b7dd1f972ea77053a9`, matching the preserved inventory. [Inspection](read-failure-file-inspection.json). This does not establish child-side allocation or read success.

The sampled VM peak was **3,221,225,472 bytes**, exactly the configured AS cap. That supports address-space pressure as a plausible explanation, but it does not identify the failed allocation/read or prove a unique cause. No errno was printed or captured. The child had already exited when the error was inspected; no tracing, replacement runtime or additional diagnostic execution was attempted. **Child-side errno remains an explicit evidence gap before any further configuration change.** No missing-file or permission-denial diagnosis is claimed.

No fresh object exists, so there is no successful object hash, resolution result or individual kernel replay. Both later stages were skipped at the first failure. The prepared checker executable remains hash-bound (`ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`), and the prepared command remains the singleton `leanchecker -v LightEFTSpanners.FiniteLaw`, with LEAN_NUM_THREADS=1 and LEAN_STACK_SIZE_KB=65536 rather than compiler-only flags. Resolver/replay would retain 128MiB and omit verbosity; neither was launched.

## Integrated preflight and exact history pass

The preflight input sweep ran once. It retained the before inventory, released the unused prior-inventory dictionary, and streamed JSON with iterative encoding rather than building a second whole JSON string. Each completed new inventory/advice log was flushed, fsynced, hashed, identity-checked and advised on the same descriptor. The final raw compiler and sample logs received the same completed-file treatment. All seven completed-file records reconcile to their final bytes and stable identities.

[runner-changes.diff](runner-changes.diff) records narrow integration into the existing supervisor. [Focused harmless tests](harmless-tests.json) passed whitelist rejection, rejection of a hash mismatch before advice, fixture-byte preservation, and fsync → hash → advice plus preflight-files → history → fresh gate ordering. Fixture data is preserved. No compiler or production history pass ran in those tests.

Immediately before compile admission, under the same universal exclusive lock, the single fixed history pass verified and advised exactly **1,560 files totaling 710,100,227 bytes**. The [whitelist](history-whitelist.json) was generated from and hash-pinned to the raw reconstruction entries and published chunks of these exact manifests:

- `7ec594260eea20cc893fa2030179d98e1a2eb0a8`: light-eft-3gib-import-result-20261017/chunks/manifest.json
- `5ffa5b72db912bfa251a07c9aacb42a67a47464e`: light-eft-finitelaw-bounded-chain-20261017/chunks/manifest.json
- `8f5f4c80e6bd86074b0fee59ec2aa728c9e23d4e`: light-eft-finitelaw-arena128-chain-20261017/chunks/manifest.json
- `33632afc3570d5c938f37560b04855f04f2e4415`: light-eft-finitelaw-arena128-advised-chain-20261017/chunks/manifest.json

There was no recursive expansion. Every historical file's hash/size matched its published entry, with stable same-descriptor identities before/after its one DONTNEED call. All 1,560 records are in [history-advice.jsonl](history-advice.jsonl). The one-use marker prevents another history pass. No historical data was removed or rewritten.

| Observed around the fixed history pass | Bytes |
| --- | ---: |
| Visible headroom before | 3,541,823,488 |
| Visible headroom after | 3,963,162,624 |
| Visible current decrease | 421,339,136 |
| memory.stat file decrease | 452,595,712 |
| memory.stat anon increase | 28,672 |
| memory.stat kernel decrease | 13,475,840 |

These are measured, separately sampled counters, not an accounting identity or exclusive causal attribution. memory.stat values can lag current usage. Advice success by itself is not proof of reclamation; the observed file-counter decrease supplies the direct accounting evidence.

## Gates, actual caps and preservation

The unchanged gate required visible headroom and host MemAvailable each at least **3,758,096,384 bytes** after preflight/history and again immediately before exec:

| Gate | Visible headroom | Host MemAvailable |
| --- | ---: | ---: |
| Admission | 3,963,179,008 | 17,793,941,504 |
| Pre-exec | 3,958,607,872 | 17,792,098,304 |

No preflight rerun or bulky chunk publication occurred before launch. The before inventory remained available for the postflight sweep. Packaging was explicitly deferred until chain termination. Completed-file housekeeping applies to later phases in the prepared code; those phases were not executed.

Actual child soft/hard caps, independently verified through handshake and kernel prlimit before exec: AS **3,221,225,472 bytes**, CPU 60 seconds, FSIZE 16 MiB, CORE 0; wall deadline 90 seconds, monitored headroom stop floor 512 MiB. Command options remained -j1 -s65536 -M512 and strict warning flags. wait4 max RSS: 199720 KiB across launcher/payload; 250 ms sampled RSS peak: 198668288 bytes. Samples do not provide continuous peaks or syscall errno.

Before/after same-UID threads: 249; visible pids.current: 271 in both groups; pids.events max 0 unchanged. Parent OOM/kill/group counters stayed 1/1/0; child-group 0/1/0. The visible cgroup identity/limit and OOM/PID checks passed. Hidden ancestor limits remain unknown under the separately reviewed bounded-route accounting rule.

All 66983 input rows verified before and after, with byte-identical inventory files SHA256 `02421853a9f0d7fb0f593fe2bead36a310c2197255cc04218526353ff92a2af7`. [392 ordered chunks](chunks/manifest.json) reconstruct inventories, advice logs and the history-pass log; all originals remain. The direct child was reaped, all descendants were gone, kernel ECHILD verified and all input-preservation checks passed. The common lock device 33/inode 3849 is free; no Lean/Lake/checker/extractor remains active. No partial output files existed. Existing scripts/__pycache__ was left untouched.

This is a bounded project compilation attempt using existing pinned dependency objects. Archive authentication remains incomplete. It establishes successful integrated housekeeping/admission and the actual arena option, followed by a compiler loading failure. It establishes no proof compilation, kernel acceptance, full clean build, CI readiness or whole-paper completion. Publish with CI skipped and stop for independent review.
