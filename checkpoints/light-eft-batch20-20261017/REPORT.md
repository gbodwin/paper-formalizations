# Twenty-module Light EFT batch: first compile passed; resolver failed closed

**No new module completed the compile–resolve–singleton-replay chain.**
`LightEFTSpanners.AdaptiveFiniteLaw` compiled successfully. Its resolver printed
the expected singleton result and was reaped with exit 0, but monitoring failed
closed on an unconfirmed two-thread terminal transition. The batch stopped at
that first failure. AdaptiveFiniteLaw replay and all three stages for the other
19 modules were skipped: two attempted children and 58 skipped stages.

The mandatory final full content check passed under the same universal lock.
No retry, resource-limit change, source repair or further Lean child followed
the failure. The previously accepted qualified FiniteLaw chain remains intact;
it is the seed, not a newly tested module in this batch.

## Exact source and outputs

- Frozen source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
- Preserved 486-source graph SHA256:
  `262e8af8f758f8d7224e8b1e7a87b4b4e8c47aab31098df3fd253af7cdbcf24c`.
- AdaptiveFiniteLaw submitted source SHA256:
  `b7de9b150e440f06a73f4ac813545092a6d7d80466000acea133faf1ef053648`.
- Newly compiled AdaptiveFiniteLaw object: 122,416 bytes, SHA256
  `3dd736d2a646495a70baafd47334f13455fb80c66a9bc454c583d5460b3c33c0`.
- Accepted FiniteLaw seed: 254,600 bytes, SHA256
  `04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc`.

The twenty exact names, order, source hashes and imports are in `PLAN.json`.
Their bindings were checked against the preserved source graph and frozen Git
source. Each project import belongs to FiniteLaw or an earlier module in the
requested order; the batch is project-dependency-closed. `module-status.json`
lists every actual failed/skipped stage and has `accepted: false` for all twenty.

The fresh output root is
`/workspace/light-eft-verification/.lake/light-eft-batch20-20261017-8467009921e24533b194577021815bab/objects`.
It began with only the hash-identical FiniteLaw seed. The original object root
was excluded from search and preserved unchanged. All project-object searches
used the fresh root plus the existing pinned dependency/toolchain roots.
Both resulting objects are preserved in `preserved-objects/`, with exact hashes
and identities in `output-records.jsonl`. The failed resolver's generated JSON
is retained in `resolutions/`; its content does not turn the failed stage into
an accepted resolution.

## Whole-batch lock and amortized preservation

One original universal lock, device 33 / inode 3849 / descriptor 3, was held
from `2026-10-17T18:02:14.150818+00:00` through release at
`18:03:48.404230 UTC`, including initial verification, both children, all
between-child checks and final verification. Supervisor PID was `161710`.
Child receipts reference the same outer acquisition time; they do not claim
independent lock releases. Kernel ECHILD was verified before final release.

There is one canonical inventory, `inputs.jsonl`: 74,609 rows, 27,386,196 bytes,
SHA256 **`50a2e51d63e167bbf4410dbb84b59b3724071be2daff59ea7ea577fd3611ac2d`**.
Full initial verification completed at `18:02:48.062900 UTC`. The final pass
attempted all 74,609 paths and produced the same digest, with no changes; it
completed at `18:03:44.321873 UTC`, before release. Final membership, pins and
small project-object checks also passed. There are exactly two full frozen-input
content passes. Publication reconciliation reads the canonical inventory and
receipts without performing a third content pass over the frozen inputs.

Between children, the controller checked identities, input/search membership
and all nine dependency revisions/tracked sources. It hashed submitted sources,
the small harness and all project objects, and tracked generated resolution
bindings separately. Each source snapshot is stored once by hash in `sources/`;
receipts reference it and the canonical inventory. Outputs have compact versioned
records. Prior evidence is referenced rather than copied into per-child input
inventories or hundreds of duplicate chunks. The four additional source files
already present outside the graph were preserved as inputs and were not built.

Focused harmless tests passed before Lean execution: shared-lock lifetime across
two children and final verification; changed input preventing spawn and failing
final comparison; and guard-failure cleanup retaining exclusion until reaping.
These tests have three cases, four receipts and three actual harmless Python
children, with synthetic accounting explicitly labeled. The changed fixture
input is intentional and confined to its fixture directory. No extra Lean
diagnostic pilot ran. The nine copied resource/sampling/exit/reaping functions
were checked AST-identical to the reviewed implementation; six support files
were byte-identical. `preparation-checks.json` records those checks and resources.

## Actual stages and commands

| Stage | UUID / child PID | Receipt created UTC | Finalized UTC | Outcome |
| --- | --- | --- | --- | --- |
| AdaptiveFiniteLaw compile | `0e36430126b6450f9d1cbe07e12d33d8` / `161794` | 18:02:51.512911 | 18:03:07.268355 | Exit 0, compile passed |
| AdaptiveFiniteLaw resolve | `e259b81f9f434245b799c342d4b62ed4` / `161872` | 18:03:07.272650 | 18:03:20.903468 | Child exit 0, supervised stage failed |
| All checker stages | No invocation | — | — | Skipped |

All times are October 17, 2026. The batch ended at `18:03:48.404436 UTC`.
Receipt intervals include verification/advice/cleanup, not just tool execution.
They do not overlap. Both children were fully reaped with no descendants;
their between-child preservation checks passed. Final verification was required
before any module result could be accepted; none had completed all three stages.

Official Lean 4.34.0 was used. Exact executable/source hashes, twenty module
bindings and nine dependency revisions are in `source-toolchain-bindings.json`.
The compiler executable SHA256 remains
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The existing resolver harness SHA256 remains
`9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf`.

Both actual argv arrays used:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean
  -j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true
```

Compilation additionally supplied the correct source `--root`, the fresh
AdaptiveFiniteLaw output path, and its frozen source file. Resolution supplied
`scripts/LightEFTResolveCheckerTarget.lean`, with target and fresh resolution
file in its environment. `MIMALLOC_ARENA_RESERVE=128MiB` was configured for both;
compile-only verbosity confirmed `arena_reserve: 131072 KiB`. Complete argv and
environment arrays are in each receipt and `result-reconciliation.json`.

Configured resource controls stayed at 12 GiB soft/hard address space, CPU
60 seconds, wall 90 seconds, file size 16 MiB, core zero, observed RSS stop
6 GiB, per-visible-group anonymous growth stop 3 GiB and ongoing visible/host
floor 1 GiB. Compile/resolver admission and pre-exec use their reviewed 3 GiB
visible/host floor. The prepared checker retains its 4 GiB visible and 3 GiB
host gate, but no checker ran. Both actual children had matching launcher and
parent kernel limit readbacks, isolated identity/session/group and inherited
lock verification. Each had its own fresh pre-exec per-group anonymous baseline.
Monitoring targeted 100 ms with full memory.stat retained. Sampled controls
are not continuous hard RSS caps; `-M` remains an intermittent runtime check.

| Stage | Visible admission / pre-exec | Sampled RSS peak | wait4 RSS bytes | Lowest sampled visible headroom |
| --- | ---: | ---: | ---: | ---: |
| Compile | 4,714,987,520 / 4,710,699,008 | 2,817,036,288 | 2,825,392,128 | 2,135,810,048 |
| Resolve | 4,716,871,680 / 4,712,079,360 | 923,332,608 | 922,935,296 | 4,512,956,416 |

## Exact resolver stop and classification

The resolver raw log contains:

```text
PASS: official checker resolution is exactly [LightEFTSpanners.AdaptiveFiniteLaw]
```

However, the sample at `2026-10-17T18:03:15.956014+00:00` retained:

- matching PID/start time, parent, session and group;
- state `Z`, PF_EXITING set, zero stat virtual size and RSS;
- **two threads** in both stat and status;
- null VmRSS/VmSize with the original raw stat/status text;
- three owned `waitid(... WEXITED|WNOHANG|WNOWAIT)` probes, all returning no
  terminal confirmation;
- a child FD probe returning `PermissionError`.

The approved unconfirmed transition allowance requires exactly one thread.
The predicate therefore remained false and missing-memory errors were not
waived. The supervisor captured the exact partial decision, sent owned-group
SIGKILL before persisting it, completed cleanup and reaped exit 0. Signal
delivery is recorded; it is not established as the cause of termination because
the recorded exit was 0, not a signal exit. No numeric memory breach was claimed:
the stop sample's visible headroom was 4,660,285,440 bytes.

`resolver-stop-sample.json` is the readable export, byte-for-structure identical
to the receipt's latest/stop decision and last runtime sample. The original
raw logs, full traceback, confirmation attempts, timings and snapshots remain
in the two attempt directories. This is a monitor condition outside the
approved allowance, not an elaboration failure, kernel rejection or a
mathematical/paper counterexample. No automatic exception broadening or retry
was performed. Compiler and resolver diagnostics have zero anchored Lean warning
headers; allocator statistics are not Lean warnings.

## Scoped advice, publication and qualifications

Two idle advice passes used only first-pass verified bindings, with same-FD
regular-file/mode/identity checks and no byte rehash. The ordinary scope was
exactly the prior 66,961 dependency/tool paths, and the data scope was exactly
the prior 7,129 advised evidence paths: no new paths. Each pass covered
11,790,867,848 bytes; its scope identity digest and full capacity observations
are in `cache-advice.jsonl`. Measured visible-current reductions were
4,701,130,752 and 2,242,973,696 bytes respectively. These measurements are not
claims that all advised bytes were reclaimed or a unique causal attribution to
each file. No speculative cache credit was used. Actual admission was checked
after the idle pass; no resource failure was retried.

One canonical inventory, compact stage/output records, raw receipts and unique
source snapshots form the evidence. `result-reconciliation.json` and
`module-status.json` summarize actual acceptance and skips. `PUBLICATION.json`
binds the result commit; `evidence-sha256.json` covers all published checkpoint
files except itself and Python bytecode caches. Object payloads are explicitly
included despite the normal ignore rule. Unchanged prior evidence is referenced
at `e18efcc0ba7ba564eacaf28b7c21a3952fee34f0`.

Dependency-cache archive authentication remains historically incomplete;
visible accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`.
The final exhaustive axiom/owner audit, a coordinated clean CI validation and
paper-level review remain outstanding. No new recursive audit or CI run occurred,
and no website or proof source changed. This is the ordinary Light EFT project
only. The worker stops after CI-skipped publication with no compiler/checker
running and the common lock free, awaiting independent review of this preserved
two-thread exit-transition blocker.
