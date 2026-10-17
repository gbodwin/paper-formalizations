# FiniteLaw: compilation passed; resolver telemetry failed closed; replay skipped

**This chain did not pass.** The fresh `LightEFTSpanners.FiniteLaw` compilation
succeeded and produced a new object. The official resolver then printed the
expected singleton result and was reaped with exit 0, but its monitor captured a
status sample missing required `VmRSS` and `VmSize` fields. The supervisor failed
closed, sent SIGKILL to the owned group, and stopped the chain. The resolver stage
is not accepted as passed. **No kernel replay ran.** No retry, cap increase, or
guard repair followed this failure.

The recorded exit was 0, not a signal exit. A successful `killpg` call does not
establish that SIGKILL caused termination. The partial sample reported state `R`
and retained the original stat/status bytes. An exit-transition explanation is
plausible but not established here; the missing telemetry was not waived.

## Frozen source and fresh output

- Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
- FiniteLaw source SHA256:
  `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`.
- Official Lean 4.34.0 executable SHA256:
  `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Official checker executable SHA256:
  `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`.
- Resolver source SHA256:
  `9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf`.
- Fresh object: 254,600 bytes, SHA256
  `04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc`.

The original output root is
`/workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-f23bcfb0a9df41ef888a8b33de4130f3/objects`.
It began empty. The only project object was newly compiled into that root; its
hash and identity stayed unchanged through resolution. A byte-identical copy
is published at `preserved-outputs/LightEFTSpanners/FiniteLaw.olean`.

The evidence directory is
`/workspace/light-eft-verification/checkpoints/light-eft-finitelaw-admission3-chain-20261017`.
Previous attempt `933e3496aaee49b38093699589d74c3b` and its complete published
checkpoint at `6697a0828656f64e138f6c77c7036397af1aa227` remain unchanged.

## Authorization, preparation and execution

Independent review of the preceding runner and all seven harmless fixture
receipts authorized this one new chain. The only runner changes were
`ADMISSION_HEADROOM = 3221225472` and the fresh output path; all nine copied
support/whitelist files are byte-identical to the reviewed checkpoint.
`approved-changes.diff` preserves that narrow difference. Four pure boundary
assertions check visible and host memory exactly at 3 GiB and one byte below it.
The earlier live fixture suite was not repeated.

Before execution, preparation observed 3,898,064,896 bytes visible headroom,
17,898,319,872 bytes host available memory and 9,582,465,024 bytes disk free.
No compiler/checker/tracer was active, and the existing universal lock was free.
The one-shot chain was invoked once:

```text
python -u checkpoints/light-eft-finitelaw-admission3-chain-20261017/chain.py
```

Its stdout/stderr is preserved in `invocation.log`. No default Lake build,
dependency rebuild, CI, tracer, runtime shim, or parallel worker was used.

| Stage | UUID / child PID | Receipt created UTC | Receipt finalized UTC | Result |
| --- | --- | --- | --- | --- |
| Compile | `4f4f6d58bd734357b8214d662c494f49` / `159386` | 16:56:34.599148 | 16:57:42.395962 | Child exit 0; supervised stage passed |
| Resolve | `70cb0c93f5c74eeaaa21d187595418ff` / `159474` | 16:57:42.470408 | 16:58:49.998384 | Child exit 0; supervised stage failed on partial telemetry |
| Replay | No invocation | — | — | Skipped after first failure |

All times are October 17, 2026. The chain ended at
`2026-10-17T16:58:50.048513+00:00`. Receipt intervals include hashing, admission,
cleanup and preservation, not just compiler elapsed time. The supervisor PID
was `159338`. Both stages used lock device 33 / inode 3849, inherited by their
isolated child session/group. The intervals do not overlap. Direct children
were reaped, no descendants remained, and kernel ECHILD was verified before
release. Both stages verified unchanged inputs and all nine dependency pins.

## Commands, configured controls and actual readbacks

The exact argv arrays and environments are in each stage's receipt and in
`result-reconciliation.json`. The actual commands were the official executable
with these argument arrays, described below without shell quoting ambiguity:

```text
compile:
  /workspace/toolchains/lean-4.34.0-linux/bin/lean
  -j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true
  --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners
  -o ORIGINAL_OUTPUT_ROOT/LightEFTSpanners/FiniteLaw.olean
  /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean

resolve:
  /workspace/toolchains/lean-4.34.0-linux/bin/lean
  -j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true
  /workspace/light-eft-verification/scripts/LightEFTResolveCheckerTarget.lean
```

`ORIGINAL_OUTPUT_ROOT` is the exact fresh object root specified above. Both
stages used `MIMALLOC_ARENA_RESERVE=128MiB`. Only compilation enabled allocator
verbosity; its log confirmed `arena_reserve: 131072 KiB` and two reservation
messages of that size. No allocator-verbosity readback was sought for resolution.
The configured Lean stack/thread/`-M` options are not kernel limit readbacks.

Both launchers and parent kernel checks verified soft/hard limits of 12 GiB
address space, 60 seconds CPU, 16 MiB file size and zero core size before exec.
The inherited lock, PID/PPID, session/group and child identity checks passed.
The wall deadline remained 90 seconds; sampling targeted 100 ms. External stops
remained 6 GiB observed RSS, 3 GiB anonymous growth **separately per visible
cgroup**, and 1 GiB ongoing visible/host headroom. Admission and pre-exec used
the new 3 GiB floor for both visible and host memory. Each stage recorded its
own fresh anonymous baseline immediately before exec; no group totals were
summed and no speculative cache credit was used.

| Stage | Admission visible / host bytes | Pre-exec visible / host bytes |
| --- | ---: | ---: |
| Compile | 3,770,667,008 / 17,742,839,808 | 3,765,731,328 / 17,745,317,888 |
| Resolve | 3,768,057,856 / 17,785,020,416 | 3,763,679,232 / 17,780,404,224 |

| Stage | Sample count | Sampled RSS peak | wait4 RSS high-water bytes | Lowest sampled visible headroom |
| --- | ---: | ---: | ---: | ---: |
| Compile | 67 | 2,824,192,000 | 2,836,979,712 | 1,180,848,128 |
| Resolve | 28 | 922,836,992 | 922,484,736 | 3,564,892,160 |

The maximum observed anonymous growth was 247,042,048 bytes in each visible
group during compilation and 148,373,504 in each during resolution. These are
individual sampled group changes relative to distinct fresh baselines, not
summed or continuous process peaks. Sampled RSS can overshoot between samples;
`-M5120` is an intermittent runtime check, not a kernel heap limit.

## Exact failure and diagnostic classification

At `2026-10-17T16:58:17.663682+00:00`, the resolver sample retained both errors:

```text
{'operation': 'VmRSS', 'error': 'Missing required live value'}
{'operation': 'VmSize', 'error': 'Missing required live value'}
```

The child state was `R`, with `rss = null` and `vm = null`; the original
`partial_stat` and `partial_status` are preserved. Accounting collection was
complete. The exact partial decision is identical in the last sample-log line,
the receipt's `latest_decision_sample` and `stop_decision_sample`, and the
readable `resolve-stop-sample.json` export. The reviewed runner retained it in
memory before evaluation and issued the owned-group SIGKILL before persistence.
No numeric RSS, anonymous-growth or headroom breach was claimed as the reason
for this stop.

The resolver's raw output is:

```text
PASS: official checker resolution is exactly [LightEFTSpanners.FiniteLaw]
```

`official-resolution.json` records exactly that one target and the new object
path. Offline reconciliation confirms its content matches the preserved fresh
object. **This does not turn the failed supervised resolver stage into a pass.**
The chain did not reach its post-stage resolution acceptance gate or invoke
`leanchecker -v LightEFTSpanners.FiniteLaw`. Checker thread/stack settings stayed
prepared configuration only, with no checker child or checker readback.

Compilation and resolver logs contain zero anchored Lean warning headers;
compilation used strict warning flags. Allocator option/statistics output is
not a Lean warning. The resolver stop is a monitoring failure, not a Lean
elaboration error, kernel rejection or mathematical counterexample. No new
recursive axiom audit ran in this attempt, so there is no fresh audit coverage
or individual kernel-replay acceptance to claim.

## Finite advice scope and actual accounting

The existing toolchain whitelist stayed at 12,594 pinned objects / 2,212,380,925
bytes per idle phase, SHA256
`ac8ff793992fec47cbac50629be8e3835b6f81328804b4662a4d6a94e60b65af`.
The existing inventory-derived scope was not expanded. Both idle before/after
passes of both attempted stages verified hashes and identities and successfully
advised the exact objects: 50,376 calls in four existing phases, zero errors.
Executables and shared libraries were excluded. No extra live diagnostic,
separate cache inventory hunt or additional advice sweep was introduced.

| Toolchain segment | Visible current before minus after, bytes |
| --- | ---: |
| Compile before | -15,200,256 |
| Compile after | -11,448,320 |
| Resolve before | -14,938,112 |
| Resolve after | -11,460,608 |

All four measured changes are increases in usage, not reclaimed bytes.
Successful advice does not establish reclamation; counter changes cannot be
uniquely attributed to advice. The one authorized historical pass covered
407 files / 183,081,165 bytes and observed a reduction of 73,728 visible-current
bytes. It ran only before compilation. Completed-file housekeeping is also
recorded for seven compile-stage files and six resolver-stage files.

## Evidence, provenance and pause

`result-reconciliation.json` binds commands, source hashes, receipt intervals,
limits, metrics, exact stop capture and cleanup. `source-toolchain-object-hashes.json`
binds the proof, resolver, executables, manifest/toolchain files and both object
copies, and records the nine unchanged dependency revisions. Source snapshots,
original raw logs, runtime sample logs, before/after inventories and advice
JSONL are retained. The inventories have 66,985 compile rows and 66,986 resolver
rows; each stage's before/after pair is byte-identical. `chunks/manifest.json`
provides 893 ordered chunks with reconstruction hashes for the large streams.
Concatenate each list's bytes without separators. The raw object is deliberately
included despite the repository's ordinary `*.olean` ignore rule.

`PUBLICATION.json` binds the result commit and scope. `evidence-sha256.json`
covers every published checkpoint file except itself and Python bytecode
caches. Earlier proof source, pins, partials and evidence remain unchanged.
The preceding reporting correction remains in the prior published report;
this continuation concerns FiniteLaw only and makes no unrelated checkpoint
claim.

Dependency caches retain their historical incomplete archive-authentication
qualification. Visible accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen
limits UNKNOWN`. Earlier syscall/telemetry qualifications are preserved and
are not retroactively resolved by this attempt. The proof's mathematical
hypotheses are unchanged; no stronger paper theorem or acceptance follows from
this compiler result. This is not a full clean build, CI pass, completed kernel
validation chain, or paper completion.

The worker is paused after publication, with no local compiler/checker/tracer
running and the universal lock free. Further execution or a monitor change
requires new authorization after review of the preserved partial sample.
