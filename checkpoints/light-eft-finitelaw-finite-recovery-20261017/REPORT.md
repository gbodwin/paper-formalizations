# FiniteLaw singleton checker passed after one finite cache-recovery pass

**The official singleton kernel checker passed against the accepted pinned
FiniteLaw object.** The child exited 0 and its entire raw output was exactly
`replaying LightEFTSpanners.FiniteLaw` followed by a newline. This attempt did
not recompile or rerun the resolver. It reused their independently reviewed
bindings only after reverifying source, object and exact singleton resolution.
No execution retry or resource-limit increase occurred.

This is a bounded, incremental module result. It is not a new clean dependency
build, CI result, recursive axiom audit, whole-project acceptance or paper
completion. The preceding failed attempts and provenance qualifications remain
preserved.

## Exact bindings and invocation

- Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
- FiniteLaw source SHA256:
  `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`.
- Pinned object: 254,600 bytes, SHA256
  `04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc`.
- Official Lean 4.34.0 executable SHA256:
  `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Official checker executable SHA256:
  `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`.
- Accepted compile/resolution evidence authority:
  `d5798e2b3d8119651e351359f42062cd826e05f5`.
- Checker attempt UUID: `4c4eea288fee436fa422bf764fcdd0ba`.
- Supervisor / child PIDs: `160915` / `160954`.

The original object remains at
`/workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-f23bcfb0a9df41ef888a8b33de4130f3/objects/LightEFTSpanners/FiniteLaw.olean`.
It was a pinned input, not an output of this attempt. Its bytes and recorded
device/inode/size/mtime/ctime identity stayed unchanged. The old published object
copy and all earlier compile/resolver receipts remain in the repository.

The new work directory is
`/workspace/light-eft-verification/.lake/finitelaw-finite-recovery-20261017-c5addd9b0ee743b596c5149baf2809d1`.
It received only a byte-identical copy of the accepted resolution record. The
evidence directory is
`/workspace/light-eft-verification/checkpoints/light-eft-finitelaw-finite-recovery-20261017`.
The one-shot entry point was:

```text
python -u checkpoints/light-eft-finitelaw-finite-recovery-20261017/chain.py
```

Its only Lean-tool invocation was exactly:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/leanchecker -v LightEFTSpanners.FiniteLaw
```

The receipt contains the full argv and environment, including the original
pinned object root first in `LEAN_PATH`, the existing dependency roots,
`LEAN_NUM_THREADS=1`, `LEAN_STACK_SIZE_KB=65536` and
`MIMALLOC_ARENA_RESERVE=128MiB`. These are configured runtime settings, not new
allocator/thread-stack readbacks. No compiler CLI flags were supplied to the
checker. No compiler or resolver executable ran in this continuation.

## Review carried forward and bounded changes

The user reports independent acceptance of the earlier compilation, exact
resolution, exit-handling repair and eleven focused fixtures. That review is
recorded as prior source/log/hash reconciliation, not fresh execution here.
`accepted-bindings.json` pins the accepted compile receipt, resolver receipt,
resolver raw output and exact resolution record to their bytes at the authority
commit. Their bindings and the current target singleton inventory were checked
before execution and again in preservation checks. The prior resource-stopped
checker is not retrospectively marked passed.

The exit-transition helper, child limiter and existing cache-advice helper are
unchanged. The new changes add the finite data pass, split visible/host admission
thresholds, and retain complete memory.stat dictionaries and raw text. Pure
boundary assertions verify visible 4 GiB and host 3 GiB gates independently,
including equality and one-byte shortfalls; compiler and resolver routes are
disabled. No new live fixture suite or live diagnostic experiment was run.
`reviewed-changes.diff` and the source-bound input inventory retain the exact
controller changes.

## Finite recovery scope and exclusions

The pass used only the `evidence-sha256.json` entries at authority commit
`d5798e2b3d8119651e351359f42062cd826e05f5` for the fifteen checkpoint roots
enumerated in `recovery-plan.json`. Their combined ceiling was exactly
**7,313 entries / 3,104,249,317 bytes**. The plan is pinned by SHA256
`a0c6b1c10e7ce61df406d68f1b84b6418b3f1acb4d925c5fb20f6ea76a42e335`.
No broader filesystem scan or cache inventory hunt supplied recovery targets.
The ordinary reviewed source/dependency input verification remained in place.

| Disposition | Files | Bytes |
| --- | ---: | ---: |
| Stream-hashed and advised | 7,129 | 3,078,727,377 |
| Excluded | 184 | 25,521,940 |
| Authority total | 7,313 | 3,104,249,317 |

Exclusions were 162 code/object/nondata-extension files, 17 source-text files
and five current bound data inputs. All five are identified in the compact pass
log and the current input inventory. Symlink, nonregular, executable-mode,
changed-identity/size/hash and binary-content exclusions were also enforced;
none added further exclusions in this actual pass. Nothing was deleted,
rewritten or truncated.

Each advised file was opened without following a final symlink, checked as a
regular nonexecutable data file, streamed for SHA256 and text/binary checks,
compared with the committed expected size/hash and the pinned identity, then
advised on the same descriptor. Identity was checked again after advice. The
log records each exact path and disposition. No executable, object, code or
current bound input was advised by the new pass.

The one-pass marker is consumed. The compact log is 3,074,720 bytes, SHA256
`0a89e8e23466513f3599c47e1fb09d8bafebabec0ae2c25e4320e980a7feefdc`.
It was completed, flushed, fsynced, stream-hashed and itself advised on the same
descriptor before the after-pass capacity sample. Receipt timestamps prove
that ordering. No large publication or reconstruction copy was generated before
admission; chunk generation occurred only after the checker and cleanup ended.

## Actual capacity, gate and unchanged runtime bounds

Before the pass, after ordinary input verification and housekeeping, visible
headroom was **2,806,743,040 bytes**. The pass ran from
`17:34:42.890693` to `17:34:47.961537 UTC` on October 17, 2026.
Its after-pass sample measured **4,443,721,728 bytes**, an observed visible-current
reduction of **1,636,978,688 bytes**. This measured change is not a claim that
all advised bytes were reclaimed, nor a unique attribution to individual files.
No speculative cache credit was used.

| Fresh gate | Visible headroom bytes | Host available bytes | Required visible / host |
| --- | ---: | ---: | --- |
| Admission at 17:34:47.988119 UTC | 4,443,586,560 | 17,793,069,056 | 4 GiB / 3 GiB |
| Pre-exec at 17:34:48.135315 UTC | 4,439,322,624 | 17,790,603,264 | 4 GiB / 3 GiB |

Both actual gates passed without lowering either threshold. The visible floor
is 4,294,967,296 bytes; host admission remains 3,221,225,472 bytes. The ongoing
visible/host floor remains 1,073,741,824 bytes. Other reviewed controls remain:
12 GiB soft/hard address space, 60 seconds CPU, 90 seconds wall, 16 MiB output
file size, zero core size, 6 GiB sampled RSS stop, and 3 GiB anonymous-growth
stop separately for each visible cgroup. A fresh checker pre-exec anonymous
baseline was recorded for each group, without summing them. Monitoring targeted
100 ms. Sampled guards can overshoot between observations; they are not kernel
hard RSS limits.

Both launcher and parent kernel checks confirmed the configured resource limits,
isolated PID/session/group identity and inherited universal lock before exec.
The existing lock device 33 / inode 3849 remained in use. No parallel worker,
compiler, resolver, default Lake build, tracer, runtime shim or CI ran here.

## Checker result and raw evidence

The receipt was created at `2026-10-17T17:34:09.773953+00:00`, finalized at
`17:35:29.074520 UTC`, and the one-shot chain ended at `17:35:29.122641 UTC`.
These intervals include verification, recovery and cleanup, not only checking.
There are 71 runtime samples from `17:34:48.015989` through
`17:34:54.840426 UTC`.

- Sampled RSS peak: 2,426,605,568 bytes.
- Owned wait4 RSS high-water: 2,426,212,352 bytes.
- Lowest sampled visible headroom: 1,980,600,320 bytes, above the 1 GiB floor.
- Maximum sampled anonymous growth: 117,088,256 bytes in each visible group,
  compared independently with its own fresh baseline.

At `17:34:54.840381 UTC`, owned non-reaping waitid confirmed CLD_EXITED/status 0.
Owned wait4 then reaped the same child with exit 0 and matching status, retaining
resource usage. Raw terminal null memory fields are preserved; no zeros were
substituted. No one-second transition wait was needed in this actual run.
The full cleanup barrier verified no descendants and kernel ECHILD before
releasing exclusion. Input and object preservation checks passed.

The complete raw checker diagnostic is:

```text
replaying LightEFTSpanners.FiniteLaw
```

There were zero warning headers. The official exact singleton target and this
successful replay are now linked to the previously accepted compilation of the
same object. This continuation adds one checker invocation and zero compiler,
resolver or recursive-axiom-audit invocations. Mathematical hypotheses are
unchanged; there is no new claim about an untested theorem, paper or audit
closure.

Full memory.stat dictionaries (61 fields per visible node in this environment)
and original raw text are retained in admission, pre-exec and every runtime
sample. This includes mapped, dirty/writeback, active/inactive file and both
slab fields. `capacity-evidence.json` exports recovery before/after, admission,
pre-exec and the minimum-headroom sample; `checker-terminal-sample.json` exports
the terminal confirmation. There was no stop sample in this successful attempt.

The ordinary existing toolchain verification/advice scope remained at 12,594
objects / 2,212,380,925 bytes per idle phase. Its two phases made 25,188 successful
calls; their measured visible-current changes were increases of 15,200,256 and
8,515,584 bytes. Those are separate from the new measured finite recovery.
No additional historical 407-file pass ran.

## Publication and retained qualifications

The 67,011-row before/after input inventories are byte-identical, SHA256
`07842a80fb0bc2ccfce3d32df13dc17ad8f240e4d35542f2eb799533dc295757`.
All nine dependency revisions and tracked sources remain pinned and unchanged.
`source-toolchain-object-hashes.json`, `accepted-bindings.json`,
`result-reconciliation.json`, the original receipts/logs and recovery plan/log
provide the exact bindings and commands. `chunks/manifest.json` lists 487
ordered byte chunks and reconstruction hashes for the large evidence streams.
Concatenate listed bytes without separators; individual chunks may split JSON
tokens or rows. `PUBLICATION.json` binds the result commit and
`evidence-sha256.json` hashes every published checkpoint file except itself and
Python bytecode caches.

The initial publication whitespace check stopped before a commit because some
byte chunks end inside JSON indentation and the preserved raw patch contains
diff-context spaces. These evidence bytes are intentionally unchanged.
`publication-checks.json` retains the diagnostics and the successful check
excluding only the specifically identified chunk/patch data paths.

Dependency cache archive authentication remains historically incomplete.
Visible accounting remains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`.
The accepted compile/resolution and old failed checker receipts are not replaced
or reclassified. Earlier syscall, telemetry and reporting qualifications remain
available in their original evidence. This publication is CI-skipped and awaits
independent review of this bounded module result. No whole-paper acceptance is
claimed. The worker stops after publication with no compiler/checker/tracer
running and the common lock free.

A reported disconnect at 17:41 UTC occurred after both the finite pass and
successful checker/cleanup had completed. At 17:42:11 UTC, tools were usable,
no compiler/checker/tracer was active, and the existing lock was free. No pass
or checker was restarted. `disconnect-reconciliation.json` records the
preserved execution times and that status check; publication continued under
the existing authorization.
