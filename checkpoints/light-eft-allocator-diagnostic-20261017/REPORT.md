# One bounded Lean version allocator diagnostic

Result: **SIGABRT (-6), with a directly logged 1 GiB mimalloc reservation**. One authorized diagnostic invocation; no import, proof compilation, checker, retry or CI. Frozen production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`. Prior result and reporting correction remain unchanged.

## Exact execution

Attempt `852b76486e464510b3dc5cdb54220db8`, child PID 152879. Supervisor began 2026-10-17T14:09:32.060608+00:00 and finalized 2026-10-17T14:10:33.157040+00:00; this includes the preserved pre/post hash phases. The child wall deadline alone was 15 seconds, not a 15-second deadline on inventory hashing.

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean --version
```

Pinned executable SHA256: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Explicit environment is the prior LANG/LC_ALL/LEAN_SYSROOT/LEAN_PATH/LEAN_SRC_PATH allowlist with **only MIMALLOC_VERBOSE=1 added**. Full values are in the receipt. There is no `-s` option or import argument in this diagnostic.

The existing verified pre-exec handshake and independent kernel limit readback enforced soft=hard AS 1,610,612,736 bytes, CPU 10 seconds, FSIZE 16,777,216 bytes, CORE 0. The unchanged admission gate was 2 GiB visible headroom (observed 4448161792 bytes), with 512 MiB stop floor. Universal lock device 33/inode 3849 was inherited and held through reaping and preservation. Target monitor interval was reduced to 10 ms to improve ordinary mapping capture; it is not a continuous trace. Mapping logs are bounded to approximately 16 MiB with individual reads capped at 1 MiB. No tracing, permissions, credentials, security or network changes were used.

## Static ELF inspection

Before launching Lean, `readelf -lW -dW <path>` inspected the pinned executable, interpreter, and recursively resolved required libraries: 11 ELF files. Full program headers, dynamic NEEDED/RUNPATH entries, hashes and static resolution qualifications are in [elf-inventory.json](elf-inventory.json) and [elf/](elf/). No `ldd` or execution of inspected libraries was used. Static resolution is distinguished from actual runtime-loaded mappings; the sampling below did not capture the loaded Lean image.

## Raw allocator observation and interpretation

The diagnostic printed mimalloc **v3.4.4**, then:

```text
option 'arena_reserve': 1048576 KiB
mimalloc: reserved 1048576 KiB memory
libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable
```

[Full raw output](evidence/raw.log) preserves all options and diagnostics. This directly confirms the allocator reported reserving 1 GiB before the thread-creation failure under a 1.5 GiB address-space cap. It is consistent with the reviewer's early 1 GiB thread-stack explanation: simultaneous 1 GiB arena and 1 GiB stack reservations would exceed that cap even before other mappings. **This diagnostic does not itself measure the attempted thread-stack allocation, prove startup ordering, or establish the unique cause of failure.** The reviewer-supplied startup-order correction is not treated as a newly executed source verification here. A CLI stack setting was not tested again.

Four ordinary `/proc/PID/maps` samples were readable: three captured the Python launcher and the final sample was empty after exit. None captured the Lean executable mappings or a 1 GiB mapping. Their raw contents remain in [mapping-samples.jsonl](evidence/mapping-samples.jsonl). Sparse RSS/VM samples therefore cannot substitute for payload allocation evidence. wait4 max RSS 126800 KiB covers launcher and payload; it is not Lean-only RSS. This is a runtime fatal diagnostic, not a Lean theorem warning or proof failure. `--version` did not complete successfully.

## PID, OOM, preservation and cleanup

Before/after same-UID thread count: 238; visible parent and child-group pids.current: 260; both pids.max values: literal `max`; both pids.events: `max 0`, unchanged. RLIMIT_NPROC remained 71955/71955, inherited RLIMIT_STACK 8388608/unlimited. Visible parent OOM/kill/group counters stayed 1/1/0; child-group counters stayed 0/1/0. No observed PID exhaustion or new OOM event. Hidden ancestor limits remain unknown. Full memory.stat/current and PID observations are preserved in the before/after JSON files.

Before/after input inventories are byte-identical, SHA256 `01f5c400cda535744603b6ed8175145fa7f4ef91d1a08d088e03184ede7f5abb`. Existing full dependency/toolchain hash-and-advice checks were retained, with the inspected system ELF files and diagnostic sources added to preservation coverage. The 386 ordered chunks reconstruct the inventories and advice logs, while raw originals remain present. [Chunk manifest](chunks/manifest.json).

Receipt flags confirm direct child reaped, all descendants gone, kernel ECHILD verified, and preserved inputs verified. Terminal read-only checks found the common lock available and no Lean/Lake/checker/extractor process. No source changes outside this additive diagnostic checkpoint occurred.

The proposed later 3 GiB AS import was **not run** and is not authorized by this evidence publication. Stop for independent review. No import success, CI readiness, or whole-paper completion claim.
