# Bounded FiniteLaw chain: stopped at compilation failure

**COMPILE_FAILED; RESOLUTION_AND_REPLAY_NOT_STARTED.** One official compiler child exited **1**. No project object was produced. No retry or later stage ran.

Production source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`. `LightEFTSpanners.FiniteLaw` was compared byte-for-byte with that commit and remains unchanged. Source SHA256: `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`. Its actual probability proofs import only Mathlib.Probability.ProbabilityMassFunction.Integrals and Mathlib.Algebra.BigOperators.Ring.Finset.

This is the authorized **bounded route**, following accepted import evidence `7ec594260eea20cc893fa2030179d98e1a2eb0a8`, not the full clean gate. Pinned existing dependency objects were reused with full pre/post hash verification. Prior incomplete archive authentication remains incomplete. Accounting covers the reviewed visible cgroups; hidden ancestor limits remain unknown. No whole-paper, full-clean, CI, successful compilation or kernel-replay claim is made.

## Actual attempt

Attempt `1ba727105400489888fdc5e8e4bc6f83`, PID 153856; created 2026-10-17T14:23:17.775540+00:00, finalized 2026-10-17T14:24:19.575976+00:00, including pre/post hashing.

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-1a08a31c07cb4c98b415f048cce217b9/objects/LightEFTSpanners/FiniteLaw.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

The isolated output root was initially empty and was the only project-object search root. Package dependencies and the official toolchain followed it; no inherited project objects were used. The compiler hash is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` (official Lean 4.34.0). [Exact argv, environment, submitted-source binding and receipt](evidence/compile/receipt.json).

## Failure and classification

[Raw diagnostic](evidence/compile/raw.log):

```text
/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean:1:0: error: failed to read file '/workspace/toolchains/lean-4.34.0-linux/lib/lean/Lean/Parser/Term.olean.private'
```

This is one compiler input/object-loading error, not a theorem elaboration result, warning or kernel rejection. No warnings were emitted. Read-only supervisor inspection found the named file present, non-symlinked and readable: 5,288,376 bytes, SHA256 `91345bf1d3fcff899c2115fa9d3d26d9d6a7604112bc4b4b5db659d41633ca2c`, matching preflight and preserved postflight bytes. [File inspection](read-failure-file-inspection.json). The precise child-side cause is undetermined; no missing-file, corruption or address-space diagnosis is asserted.

The output inventory is empty, so there is no fresh-object hash, resolver result or individual kernel replay result. Both later stages were skipped. chain-result.json lists successful stages only (none); the failed attempt is fully recorded under evidence/compile. The empty fresh output directory remains preserved.

## Prepared sequencing support

[Runner changes](runner-changes.diff) narrowly add exact compile/resolver/checker plans, source/executable/harness hashes, explicit root/output, initially-empty checks, fresh-object bindings and a singleton resolution gate. The launcher, limits, monitored PID/OOM accounting, hash/advice and fail-stop cleanup are retained. Eight harmless in-process command/environment checks passed; they do not execute or validate the skipped resolver/checker stages.

The prepared official-resolution harness is unchanged: scripts/LightEFTResolveCheckerTarget.lean, SHA256 `9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf`, introduced at `a02bb55db31aa7548a683c3fe6a3827795816b0b`. The prepared checker is the pinned official executable SHA256 `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`; its only planned argv is `leanchecker -v LightEFTSpanners.FiniteLaw`. The checker environment would explicitly add LEAN_NUM_THREADS=1 and LEAN_STACK_SIZE_KB=65536, without compiler CLI flags. Neither stage ran. No aggregate-prefix replay was attempted.

## Limits and observations

Actual child AS soft/hard independently verified before exec: **3,221,225,472 bytes**. CPU 60 seconds, wall 90 seconds, FSIZE 16 MiB, CORE 0, monitored stop floor 512 MiB. Both post-preflight and fresh pre-exec gates require visible headroom and host MemAvailable of at least 3,758,096,384 bytes:

| Gate | Visible headroom | Host MemAvailable |
| --- | ---: | ---: |
| Post-preflight | 3812110336 | 17674887168 |
| Pre-exec | 3807531008 | 17674833920 |

wait4 max RSS: 133708 KiB across launcher/payload. Sparse 250 ms samples showed RSS 8130560 bytes and VM 35553280 bytes; these mainly captured the launcher and do not establish payload peaks.

Before/after same-UID threads 242, visible pids.current 264 in both groups, pids.events max 0, unchanged. Inherited NPROC 71955/71955 and STACK 8388608/unlimited, unchanged. Parent OOM/kill/group counters stayed 1/1/0; child-group 0/1/0. Full raw observations remain preserved.

## Evidence and terminal state

All 66981 input rows are unchanged; before/after inventory SHA256 `8ad437d5b1d9f3613dad4777614a36e208ae407e44ca538f377eeae4a7382160`. [386 ordered chunks](chunks/manifest.json) reconstruct inventories and advice logs. Raw originals, source snapshots, receipts and diagnostics are retained. No prior tracked source, dependency pin, partial proof or evidence was changed.

The first offline chunk export had a Path-indexing typo; its diagnostic and preliminary publication commits are preserved in [export-failed-attempt.txt](export-failed-attempt.txt). The corrected offline exporter reconstructed and hash-checked all chunks. This packaging repair did not rerun Lean. The final manifest supersedes the incomplete preliminary publication manifest without deleting history.

Direct child reaped, all descendants gone, kernel ECHILD verified, inputs preserved. Universal lock device 33/inode 3849 is free and no Lean/Lake/checker/extractor process is active. No partial output files existed. Existing scripts/__pycache__ was left untouched. No retry, cap increase, CI dispatch or later proof work. Publish with CI skipped and stop for independent review.
