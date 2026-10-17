# Whole-process repair and 59-stage resume: two qualified chains completed

**AdaptiveFiniteLaw and FiniteHoeffding completed their required validation
chains, with final full preservation verified.** ProductSampleConcentration
compiled, but its resolver hit a remaining lifecycle bookkeeping gap and the
batch stopped immediately. Seven of the 59 requested stages ran; 52 were
skipped. ProductSampleConcentration replay and all stages for the remaining
17 modules did not run. No stage was retried and no cap was changed.

This is a qualified incremental module result awaiting independent review,
not a clean dependency build, coordinated CI result, final exhaustive audit or
paper-level acceptance. The accepted FiniteLaw and AdaptiveFiniteLaw objects
were copied into a fresh root; neither was recompiled. All previous failed
receipts, objects and evidence remain unchanged.

## Exact source, graph and outputs

- Frozen source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
- Preserved 486-source graph SHA256:
  `262e8af8f758f8d7224e8b1e7a87b4b4e8c47aab31098df3fd253af7cdbcf24c`.
- FiniteLaw seed: 254,600 bytes, SHA256
  `04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc`.
- AdaptiveFiniteLaw seed: 122,416 bytes, SHA256
  `3dd736d2a646495a70baafd47334f13455fb80c66a9bc454c583d5460b3c33c0`.
- Fresh FiniteHoeffding object: 253,688 bytes, SHA256
  `44c7650836db9eca216944513df76b48e9fd74f040d95351e72a1207238d03e8`.
- Fresh ProductSampleConcentration object: 145,664 bytes, SHA256
  `37324c16372f539577e12ee4c636dd9fc135e72d2aa076a09b54ffa88c6979c8`;
  successful compilation only, not a completed singleton replay.

The fresh output root is
`/workspace/light-eft-verification/.lake/light-eft-batch20-wholeprocess-20261017-d6afe6aa3c6c4dcfa2540c142bf368fa/objects`.
It began with exactly the two hash-identical accepted seeds. Old roots were
excluded from search. The source graph, all requested source bindings and their
frozen Git contents were reverified; later modules have binding verification
only, not execution acceptance. `PLAN.json` gives the exact ordered modules,
imports, accepted-seed evidence hashes and 59-stage resume rule.

Four objects are preserved in `preserved-objects/` with exact versioned bindings
in `output-records.jsonl`. `module-status.json` records every reused, passed,
failed and skipped stage. The two completed names are also in the final
`accepted_modules` field; that field means the bounded chain passed its checks,
not that an independent reviewer has already accepted this new publication.

## Whole-process lifecycle repair and focused fixtures

The user reports independent acceptance of the previous AdaptiveFiniteLaw
compilation and its 74,609-binding final preservation at
`2aa14af313efacef4ecbb9900a204efbfc8ba041`. This carries forward review of old
source/log/hash evidence; it is not a fresh compilation in this continuation.
The failed old resolver remains failed and is not reclassified.

The new supervisor retains every observed TID's Tgid, start time and identity
while the process is live. It discovers through the owned task directory and
reads `/proc/TID` directly for retained siblings if the leader's task directory
becomes unavailable. TID reuse, Tgid/start-time mismatch and ownership failures
remain fail-closed. A zombie leader alone never establishes process completion.

If leader memory disappears, a live sibling with checked identity and inherited
lock supplies one shared-address-space RSS/VM sample. Samples are never summed
across threads. Raw leader/thread data and nulls remain intact. Peak/ceiling
checks use an observed identity-checked shared-mm sample; no missing value is
replaced with zero. Still-live missing telemetry fails closed. Positively
exiting/no-mm tasks get only fixed, non-resetting teardown grace of at most one
second, capped by the existing wall deadline. Accounting, headroom, anonymous
growth, descendants and deadlines continue during that grace.

Only owned `waitid(P_PID, pid, WEXITED|WNOHANG|WNOWAIT)` can confirm whole-process
termination. Owned wait4 is the sole direct-child reaper and must match that
status with exit 0 before a child passes. An exited leader's FD table is not
required; a live memory-source sibling's inherited lock is checked instead.
The parent universal lease persists through complete cleanup and kernel ECHILD.

Fourteen focused harmless fixtures passed before Lean execution. Real native
pthread workers exercise leader termination with three or two live siblings;
no C or Lean compilation is used. Fixtures cover direct live-sibling telemetry,
all-thread teardown, timeout without grace reset, live leader/sibling missing
memory, accounting/headroom/RSS failures during grace, nonzero/signal exits,
waitid ownership failure, and sibling Tgid/start-time mismatch. Synthetic fault
injections and synthetic accounting are explicitly labeled. Each fixture has
its own source-bound receipt, real waitid/wait4 and lock/reaping checks. All
children were reaped. `whole-process-fixture-results.json` lists the cases;
`lifecycle-changes.diff` and the actual helper sources show the repair. These
fixtures did not cover the within-sample stale-row case described below.

## One lease and two full content passes

The original universal lock (device 33 / inode 3849 / FD 3) was held from
`2026-10-17T18:29:14.104755+00:00` until `18:31:54.398684 UTC`, including cache
preparation, initial full verification, every child and final verification.
Supervisor PID was `162682`. The final release required kernel ECHILD.

One canonical inventory, `inputs.jsonl`, has **74,615 rows / 27,388,327 bytes**,
SHA256 **`c6ef74001a7bcbf35624556862f87e173ff939863d85631e253686815ad450cd`**.
Initial verification completed at `18:29:45.829261 UTC`. Final verification
attempted all paths and completed at `18:31:50.574776 UTC` with exactly the same
stream digest and no changes, before the lock was released. The added seed,
lifecycle and authority bindings explain the new inventory; the old 74,609-row
inventory and its earlier review remain preserved separately.

Between children, identity, input/search membership and nine pinned dependency
revisions/tracked sources were checked. Small submitted sources/harness,
project objects and generated resolution bindings were hashed. Each source
snapshot is stored once by hash. Stage receipts reference the canonical input
digest and compact output versions. No full input table is copied per child.
Publication reconciliation verifies the inventory file and saved final digest;
it does not perform a third full content pass over the frozen inputs.

At preparation, visible headroom was only 177,561,600 bytes despite host
MemAvailable of 17,900,744,704. Before allocating the new full inventory tables,
one low-memory idle advice pass streamed the independently accepted prior
canonical bindings under this new lease. Its authority inventory SHA256 was
`50a2e51d63e167bbf4410dbb84b59b3724071be2daff59ea7ea577fd3611ac2d`.
Same-FD identity/mode checks constrained it to the existing 66,961 ordinary
dependency/tool paths and 7,129 prior data paths, with no new targets and no
content certification from advice alone. New full verification still preceded
all Lean children. Measured visible-current reduction was 4,723,154,944 bytes;
after-pass headroom was 4,904,128,512. `bootstrap-recovery.json` preserves this
distinct pre-initial pass and full accounting.

Five later idle passes reused current batch verified identities over the same
scope, without rehashing bytes. Each covered 11,790,867,848 bytes; path counts,
scope digest and actual before/after capacity are recorded. There was no scope
expansion, repeated failed admission or speculative cache credit. Observed
counter changes are not claims that every advised byte was reclaimed.

## Actual seven stages

| Module / stage | UUID | Child PID | Exit / supervised outcome |
| --- | --- | ---: | --- |
| AdaptiveFiniteLaw resolve | `bcec7d0bc317424e8701337e041ef989` | 162758 | 0 / passed exact singleton |
| AdaptiveFiniteLaw replay | `3dd4c29c13e34c8fbe27f3364d30de36` | 162845 | 0 / passed singleton kernel replay |
| FiniteHoeffding compile | `bd6849ac083d4f9e89ab0c50189362f6` | 162923 | 0 / passed |
| FiniteHoeffding resolve | `7147c2b15ca5437da582ef1636540c77` | 163001 | 0 / passed exact singleton |
| FiniteHoeffding replay | `e6846cda78734a8087288f6aad6a7749` | 163088 | 0 / passed singleton kernel replay |
| ProductSampleConcentration compile | `8b697aaaad0548ca8c592035f17675b1` | 163166 | 0 / passed compilation only |
| ProductSampleConcentration resolve | `d510baecc67a445783caad57388d8374` | 163244 | 0 / monitor failed closed |

The first child receipt began at `18:29:49.619400 UTC`; the failed receipt
finalized at `18:31:29.393101 UTC`. Final preservation and release followed.
All seven receipt intervals are sequential, inherit the same parent lease,
and have source/snapshot bindings, fresh per-group anonymous baselines,
admission and limit readbacks, full memory.stat, telemetry and complete cleanup.
No later child started. The two replay logs are exactly:

```text
replaying LightEFTSpanners.AdaptiveFiniteLaw
replaying LightEFTSpanners.FiniteHoeffding
```

Each is a separate official `leanchecker -v MODULE` invocation, exit 0, with
owned waitid/wait4 status agreement. Both fresh resolutions were accepted as
exact singleton paths into the new object root. Source/toolchain/object hashes
and all nine dependency revisions are in `source-toolchain-bindings.json`.
Official Lean 4.34.0 executables remain unchanged. No source, website, runtime
shim, dependency pin or network/security setting was changed.

Compiler/resolver flags remained `-j1 -s65536 -M5120 -DautoImplicit=false
-DwarningAsError=true`, with correct source roots and fresh output paths. Both
actual compiles confirmed the 128 MiB arena setting via compile-only verbosity.
Checker invocations used their supported thread/stack environment, not compiler
CLI flags. Exact argv/environment and UTC/monotonic times are in receipts and
`result-reconciliation.json`.

Resource controls stayed at AS 12 GiB soft/hard, CPU 60 seconds, wall 90 seconds,
file size 16 MiB, core zero, observed RSS 6 GiB, and 3 GiB anonymous growth per
visible cgroup independently. Compile/resolver admission/pre-exec remained
3 GiB visible/host; checker visible gate remained 4 GiB with host gate 3 GiB;
ongoing visible/host floor remained 1 GiB. Each child had matching launcher and
parent kernel limit/identity/lock checks. Monitoring targeted 100 ms and retained
full memory.stat, including mapped, dirty/writeback, active/inactive and slab
fields. Sampling is not a continuous hard RSS guarantee, and `-M` is not a
kernel heap cap. No actual stop in this resume was a numeric resource breach.

## Remaining lifecycle bookkeeping gap

The failed resolver printed the expected ProductSampleConcentration singleton
line and was reaped with exit 0, but its supervised stage is not passed. At
`18:31:25.405888 UTC`, the initial leader read was identity-correct, state S,
five threads, RSS 921,923,584 bytes. During that same decision:

1. All four retained sibling TIDs were positively observed gone via direct TID
   paths.
2. The leader FD probe returned PermissionError; another owned waitid probe
   still returned no terminal confirmation.
3. A fresh identity-matching leader read was state R, PF_EXITING, one thread,
   zero stat memory and null RSS/VM. It started the fixed teardown grace.
4. The final fallback nevertheless classified the earlier live leader row,
   not the fresh no-mm re-read, so it raised
   `No identity-checked live shared-mm telemetry or bounded exiting-only group`
   immediately, before that grace expired.

This is the remaining stale-row bookkeeping gap in the implementation. It is
not evidence of bad proof source or a mathematical counterexample. The harness
was not patched or retried after the production failure. Future repair/review
needs a fixture for this exact within-sample live-memory → FD-loss → no-mm
transition and propagation of the fresh classification; no such extra test or
execution was performed here.

`product-resolver-stop-sample.json` is the exact readable decision, including
both leader reads, raw/null sibling data, all probes, ownership/start times and
the still-future grace deadline. It matches the receipt's latest/stop sample and
last telemetry line. SIGKILL was sent to the owned group before persistence;
its exit was 0, so signal causation is not established. Visible headroom at the
stop was 4,486,041,600 bytes. Raw diagnostics, full traceback and the failed
resolution JSON are preserved. All seven stages have zero anchored Lean warning
headers; allocator statistics are classified separately from Lean warnings.

## Disconnect, publication and qualifications

All 14 fixtures had completed by `18:25:24.831753 UTC`; preparation was recorded
at `18:27:24.196923 UTC`. The batch ended at `18:31:54.398803 UTC`, before the
reported disconnect at `18:35:50 UTC`. At `18:37:10.533482 UTC`, tools were usable,
no compiler/checker/tracer was active and the lock was free. Nothing was restarted.
`disconnect-reconciliation.json` records that check.

Execution access was confirmed recovered again during read-only reconciliation
at `18:42:56.883546 UTC`. Publication-only reconciliation subsequently passed at
`18:45:05.448630 UTC`, with no active compiler/checker/tracer and the original
common lock free. `verify_publication.py` is a post-execution, offline helper;
it was not part of the tested compiler harness. Its saved initial result is in
`publication-verification-initial.log`. This publication launched no Lean,
fixture, repair, retry, cache advice or extra full-input content pass.

One canonical input inventory, compact stage/output records, raw receipts,
unique source snapshots and four object payloads form this publication.
`thread-catalogs.json`, `module-status.json` and `result-reconciliation.json`
make the completed and failed paths reviewable without duplicating old evidence.
`PUBLICATION.json` binds the result commit; `evidence-sha256.json` covers every
published checkpoint file except itself and Python bytecode caches. Prior
evidence is referenced at its existing immutable commits.

Dependency-cache archive authentication remains historically incomplete and
visible accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`.
The final exhaustive owner/axiom audit, coordinated clean CI and paper-level
review remain outstanding. No new recursive audit or CI ran. Mathematical
hypotheses are unchanged. This is ordinary Light EFT validation only; there is
no whole-paper completion claim. The worker pauses after CI-skipped publication
with no compiler/checker running and the universal lock free.
