# FiniteLaw exit-transition repair: resolver passed; checker stopped on headroom

**Exact resolution passed. Kernel replay did not pass.** One resolver and one
singleton checker were run sequentially against the accepted, unchanged
FiniteLaw object. The resolver terminated successfully under the repaired
supervisor. The checker was stopped by the existing 1 GiB visible-headroom
guard and reaped with exit -9. No recompilation, execution retry, cap increase,
or post-failure monitor change occurred.

The checker trigger was complete telemetry, not an exit-transition exception:
visible headroom was **1,042,374,656 bytes**, below **1,073,741,824** by
**31,367,168 bytes**. Host available memory was 17,625,296,896 bytes and sampled
checker RSS was 405,020,672 bytes. No kernel-replay acceptance, full clean build,
CI pass or paper completion follows from this attempt.

## Source, object and preservation

- Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
- FiniteLaw source SHA256:
  `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`.
- Pinned object: 254,600 bytes, SHA256
  `04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc`.
- Accepted compile and preceding failed-resolver evidence:
  `5e10ed3e9cfaa2b10a4126a30d6b2ec643534a6a`.
- Original object path:
  `/workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-f23bcfb0a9df41ef888a8b33de4130f3/objects/LightEFTSpanners/FiniteLaw.olean`.

The original object root was retained as a pinned input. Its exact singleton
inventory, hash, byte count and identity were checked before each stage and
stayed unchanged through cleanup. No project object was built or replaced.
The previously published object copy remains available at
`checkpoints/light-eft-finitelaw-admission3-chain-20261017/preserved-outputs/LightEFTSpanners/FiniteLaw.olean`
in the preceding evidence commit. All older sources, pins, partials, failed
receipts and evidence are preserved unchanged.

This evidence directory is
`/workspace/light-eft-verification/checkpoints/light-eft-finitelaw-exit-transition-20261017`.
The fresh work directory is
`/workspace/light-eft-verification/.lake/finitelaw-exit-transition-20261017-9119195bfe4f419b921db2de9217e4c3`.
It holds the new resolver output, not a replacement object root.

## Focused supervisor repair

The user reports independent review accepting the earlier compilation and
identifying the earlier resolver sample as consistent with exit teardown:
matching identity, one thread, PF_EXITING, and zero stat memory fields, followed
by owned wait4 exit 0. This records review context, not a new kernel-source
investigation or a retrospective pass for that failed receipt.

`exit_transition.py` observes only the owned child, using
`waitid(P_PID, pid, WEXITED | WNOHANG | WNOWAIT)` before requiring live memory or
FD fields, and again if required memory fields or the FD become unavailable.
It never reaps. Owned `wait4` remains the sole direct-child reaper and retains
resource usage. The two kernel observations must agree on exit status.

Before kernel confirmation, the only missing-memory allowance requires the
same PID, start time, parent, session and group; stat and status thread counts
both equal one; PF_EXITING; zero stat virtual size and RSS; and no other child
collection error. That exact transition gets at most one second, bounded also
by the existing wall deadline, to obtain kernel terminal confirmation. The
timer is not restarted. A changed identity, vanished predicate, unconfirmed
timeout, live missing telemetry, accounting failure, numeric breach,
unexpected descendant, nonzero exit or signal exit remains fail-closed.

Accounting, host/visible headroom, per-group anonymous growth, numeric RSS,
descendants and deadlines continue to be checked during the interval. FD
unavailability is rechecked against kernel termination and cannot become a
general live-child exemption. Confirmed terminal children do not require live
FDs. Raw and null memory fields and original collection errors remain in the
receipt/sample log: missing values are never replaced with zero.

`reviewed-changes.diff` records changes to the reviewed runner and telemetry
collector. `exit_transition.py` and the two-stage `chain.py` are included in the
bound inputs. The compilation stage is disabled. Seven unchanged support and
whitelist files were verified byte-identical to the reviewed checkpoint.

## Harmless fixtures and preserved development failure

Eleven sequential harmless Python fixtures passed: successful bounded
transition, ordinary live missing telemetry, transition timeout, identity
mismatch, accounting failure during transition, visible/host/anonymous/RSS
breaches, nonzero exit and signal exit. They use the real owned waitid/wait4,
inherited universal lock, PID/session identities and cleanup. Synthetic
transition/accounting fields are explicitly labeled. Receipts bind child
source and supervisor/helper hashes, unique UUIDs and timing; all children were
reaped, exclusion checked and kernel ECHILD verified. The successful fixture
confirmed WNOWAIT had not reaped the child before wait4.

The first development fixture failed on a test-only `Path.exists` probe of a
confirmed terminal child's FD, which returned PermissionError. That child exited
0 and was fully reaped. The original receipt, raw traceback, child source and
matching controller/helper snapshots remain under `focused-fixtures/` and
`fixture-development-failure-001/`. The probe was corrected, and FD
unavailability was given the kernel recheck described above before the
successful new fixture suite. No Lean had run during that development failure.
`focused-fixture-results-v2.json` lists all eleven passing cases; no failed
attempt was discarded or rewritten.

## Actual resolver and checker execution

Pre-execution checks observed visible headroom 3,410,546,688 bytes, host available
memory 17,912,938,496 bytes and disk free 9,115,750,400 bytes. No
compiler/checker/tracer was active; the original lock device 33 / inode 3849 was
free. The pinned object, source, executable hashes and target inventory passed.

| Stage | UUID / child PID | Receipt created UTC | Finalized UTC | Actual result |
| --- | --- | --- | --- | --- |
| Resolve | `0bf1d361cbee424b82b49fdb5b4787c5` / `160178` | 17:14:59.621263 | 17:16:01.217489 | Exit 0, accepted exact singleton |
| Replay | `c45ddd6eb7c3466185225691bfffc272` / `160274` | 17:16:01.930162 | 17:17:06.217421 | Headroom guard, SIGKILL, exit -9; not passed |

All times are October 17, 2026. The chain ended at
`2026-10-17T17:17:06.263023+00:00`; supervisor PID was `160139`. Receipt intervals
include hashing, admission, execution, cleanup and preservation. They do not
overlap. Both inherited the same universal lock into isolated sessions/groups,
were directly reaped and had no remaining descendants. Source and all input
hashes/identities were verified unchanged after each stage; all nine dependency
revisions and tracked sources match the manifest.

The resolver argv used the official executable
`/workspace/toolchains/lean-4.34.0-linux/bin/lean` with
`-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true` and the existing
`scripts/LightEFTResolveCheckerTarget.lean`. Its environment selected the new
resolution file and original pinned object root. The checker argv was exactly:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/leanchecker -v LightEFTSpanners.FiniteLaw
```

The checker used supported `LEAN_NUM_THREADS=1` and `LEAN_STACK_SIZE_KB=65536`
environment settings, with no compiler CLI flags. Both stages configured
`MIMALLOC_ARENA_RESERVE=128MiB`. No new verbose allocator observation was made;
that setting is configuration, unlike the prior accepted compiler's allocator
readback. Exact argv/environment arrays are in the receipts and reconciliation.

Both child launcher and parent kernel checks verified soft/hard limits of
12 GiB address space, CPU 60 seconds, file size 16 MiB and core size zero, plus
PID/PPID, session/group and inherited-lock identity before exec. The wall limit
remained 90 seconds and monitoring targeted 100 ms. Admission/pre-exec remained
3 GiB for visible and host memory; ongoing floor remained 1 GiB. RSS stop
remained 6 GiB and anonymous-growth stop remained 3 GiB independently for each
visible cgroup, with fresh per-stage pre-exec baselines. No limits increased.

| Stage | Admission visible bytes | Pre-exec visible bytes | Samples | Sampled RSS peak | wait4 RSS bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Resolve | 3,291,443,200 | 3,287,265,280 | 27 | 923,324,416 | 922,918,912 |
| Replay | 3,247,685,632 | 3,243,495,424 | 54 | 405,020,672 | 405,086,208 |

The maximum sampled anonymous growth per visible group was 148,869,120 bytes
for resolution and 46,432,256 for replay. These are separate group comparisons,
not summed values or continuous process peaks. Sampled guards can overshoot
between observations; `-M` is an intermittent runtime check, not a kernel heap
cap. Hidden-ancestor limits remain unknown.

## Actual terminal confirmation and checker stop

At `17:15:31.651023 UTC`, resolver waitid confirmed CLD_EXITED/status 0 without
reaping. Its following raw status sample was a zombie with null RSS/VM values.
Those nulls and original missing-field diagnostics were retained; kernel
confirmation allowed terminal handling without a live FD check. Owned wait4
then returned exit 0 with resource usage and a matching status. **The production
resolver did not need the one-second PF_EXITING wait.** That pending path has
focused fixture coverage, not a production occurrence in this attempt.

The raw resolver output is
`PASS: official checker resolution is exactly [LightEFTSpanners.FiniteLaw]`.
The new `official-resolution.json` records exactly one module and the original
pinned object path; the chain accepted this exact result before launching the
checker. `resolver-terminal-sample.json` is the readable raw/null confirmation
export.

The checker trigger at `2026-10-17T17:16:37.054341+00:00` was a live state-S,
identity-matching child with complete telemetry and an intact inherited FD.
Waitid reported no terminal child, no transition predicate matched, and no
missing-memory allowance applied. Visible memory.max/current were
17,179,869,184 / 16,137,494,528 bytes. The sample's anon/file/kernel fields were
252,624,896 / 14,763,782,144 / 1,115,078,656 bytes. These are observations, not a
unique causal attribution to this checker or to cache advice.

The exact trigger is identical in the last runtime sample, receipt
`latest_decision_sample`, receipt `stop_decision_sample`, and
`checker-stop-sample.json`. Capture finished before the owned-group SIGKILL was
issued and before the stop decision was persisted. Cleanup recorded exit -9,
full reaping, kernel ECHILD and preserved inputs. The checker raw log is empty;
there is no completed singleton replay diagnostic or kernel result to accept.
The stop is an external resource guard, not a Lean theorem/kernel rejection.

Resolver and checker logs contain zero anchored Lean warning headers. Empty
checker output does not imply successful checking. No new compilation or
recursive axiom audit ran, so no new audit coverage is claimed. Proof hypotheses
remain unchanged; this result supplies no stronger mathematical endpoint.

## Cache scope, evidence and remaining qualification

The exact existing 12,594-object / 2,212,380,925-byte toolchain whitelist was
reused, with unchanged SHA256
`ac8ff793992fec47cbac50629be8e3835b6f81328804b4662a4d6a94e60b65af`.
Each existing idle before/after phase for both stages verified and advised the
same pinned objects: 50,376 successful calls, no errors or scope expansion,
and no executable/shared-library advice. No additional history pass ran.
Measured visible-current drops were respectively -15,200,256, -11,730,944,
-15,200,256 and -5,951,488 bytes: all were usage increases, not demonstrated net
reclamation. No speculative cache credit was used.

The original inventories/advice/sample logs, receipts, submitted sources,
fixture failure and successful fixture evidence are preserved.
`result-reconciliation.json` records the outcomes and metrics.
`source-toolchain-object-hashes.json` binds source, resolver, official Lean
4.34.0/checker binaries, pins and the unchanged object. Input inventories have
66,987 resolver rows and 66,988 checker rows; each stage's before/after pair is
byte-identical. `chunks/manifest.json` provides 891 ordered readable chunks and
whole-stream reconstruction hashes; concatenate listed bytes without separators.
`PUBLICATION.json` binds the result commit and `evidence-sha256.json` hashes all
published checkpoint files except itself and bytecode caches.

Dependency cache archive authentication remains historically incomplete.
Visible accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`.
All earlier syscall/telemetry qualifications and the prior reporting correction
are retained. This is FiniteLaw-only incremental work, not a clean/CI/paper pass.
The worker is paused after publication with no compiler/checker/tracer running
and the common lock free. The remaining blocker is the actual visible-headroom
guard during singleton replay; no execution retry or resource change is made.
