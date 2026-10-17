# FiniteLaw accounted-chain attempt: admission refused before Lean

**Result: no compiler, resolver, or checker child started.** Attempt
`933e3496aaee49b38093699589d74c3b` refused admission because visible headroom was
**3,733,762,048 bytes**, below the required **3,758,096,384 bytes** by
**24,334,336 bytes**. Host available memory was 17,716,727,808 bytes and passed
its admission test. The chain stopped at its first failure, without retry or
cap increase. No fresh object, resolution result, singleton replay, or
mathematical acceptance resulted from this attempt.

This report finishes publication of an existing attempt. No Lean, checker,
tracer, cache-advice pass, or retry was run to prepare this publication.
Independent resource review remains pending. CI is skipped.

## Exact source and attempt

- Frozen proof source: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
- Module: `LightEFTSpanners.FiniteLaw`.
- Submitted/current source SHA256:
  `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`.
- Official Lean 4.34.0 executable SHA256:
  `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Official checker executable SHA256:
  `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`.
- Attempt supervisor PID: `158456`; no compiler child PID was assigned.
- Receipt created: `2026-10-17T16:36:25.800492+00:00`.
- Admission sampled: `2026-10-17T16:36:57.357465+00:00`.
- Receipt finalized: `2026-10-17T16:37:27.575571+00:00`.
- Chain ended: `2026-10-17T16:37:27.620863+00:00`.
- Original offline reconciliation: `2026-10-17T16:42:03.249843+00:00`.

The exact output directory is
`/workspace/light-eft-verification/checkpoints/light-eft-finitelaw-accounted-chain-20261017`.
The fresh object root was
`/workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-ec7ed3c19a7e4d64ad9aa59666882e61/objects`;
it contains no files. The one-shot invocation marker is preserved and consumed.

## What ran

Preparation implemented the revised decision collection and guards, performed
syntax/preparation checks, and ran seven sequential harmless sleeping-Python
fixtures. The fixtures covered visible headroom, host availability, RSS,
anonymous growth in each of the two visible groups, missing required RSS, and
collection failure. Their exact complete or partial triggering samples were
retained before guard evaluation, the owned group was killed before sample
persistence, and children were reaped. Boundary checks include independent
per-group anonymous comparisons and fresh stage baseline reset. These are
synthetic guard tests, not Lean executions or measurements of production
anonymous growth.

The main attempt then performed the existing idle input verification/advice
phase, completed-file housekeeping and the single historical-file advice pass,
and collected a complete admission sample. Admission failed. The post-failure
idle verification/advice phase completed and verified preservation. The receipt
records `kernel_no_children_verified = true` and
`preserved_inputs_verified = true`.

| Stage | Actual outcome |
| --- | --- |
| Compile admission | Failed before spawning a child |
| FiniteLaw compilation | Did not run |
| Official exact target resolution | Did not run |
| Official singleton kernel replay | Did not run |

`chain-result.json` has an empty completed-stage list and an empty terminal
object inventory. No `raw.log` or runtime `samples.jsonl` exists for the main
attempt because no child started. `invocation.log` preserves the supervisor's
raw traceback, ending in
`MemoryGuardError('Visible headroom below required floor')`.
This is a resource admission refusal, not a Lean error, warning, kernel failure,
or theorem counterexample. There are no Lean diagnostics or warnings to classify
for this attempt because Lean did not run.

## Configured commands and guards, not observed child readbacks

The intended sequence was compile, exact official resolution, then one official
singleton replay. `chain.py`, `pilot_runner.py`, and the main receipt retain the
complete command/environment construction. The compiler argv prepared for this
attempt was:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean
  -j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true
  --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners
  -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-ec7ed3c19a7e4d64ad9aa59666882e61/objects/LightEFTSpanners/FiniteLaw.olean
  /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

Each line above is an argv description, not a shell command to run. The receipt
contains the authoritative argument array, including paths containing spaces.
Compiler/resolver configuration was `-M5120 -j1 -s65536`, with
`MIMALLOC_ARENA_RESERVE=128MiB`; verbose allocator reporting was compile-only.
The planned checker command was
`leanchecker -v LightEFTSpanners.FiniteLaw`, using its supported thread/stack
environment rather than compiler CLI flags.

| Configured control | Value |
| --- | --- |
| Address-space soft/hard limit | 12,884,901,888 bytes (12 GiB) |
| Observed RSS stop | 6,442,450,944 bytes (6 GiB) |
| Anonymous growth stop | 3,221,225,472 bytes (3 GiB), separately for each visible group |
| Visible and host admission floor | 3,758,096,384 bytes (3.5 GiB) |
| Ongoing visible and host floor | 1,073,741,824 bytes (1 GiB) |
| Sampling target | 100 ms |
| CPU / wall / file size / core | 60 s / 90 s / 16 MiB / 0 |

The intended anonymous baseline is a fresh complete pre-exec sample for each
stage. The visible groups are not summed. A complete or partial decision sample
is retained in memory before evaluation; on a breach, the owned process group
is killed before the exact triggering sample is persisted. Missing required
telemetry fails closed. Sampled RSS is not a kernel hard RSS limit and can
overshoot between samples; Lean's `-M` is an intermittent runtime check.

**None of the new child's limit, allocator, thread, stack, or PID/lock readbacks
was obtained in this main attempt.** No fresh pre-exec anonymous baseline or
runtime decision sample exists. The production admission sample itself is
complete. The revised runtime behavior has fixture coverage only here.

## Cache advice and actual accounting

The toolchain whitelist was derived from the already-inventoried immutable
objects, not a new filesystem hunt. It contains exactly 12,594 files totaling
2,212,380,925 bytes; whitelist SHA256 is
`ac8ff793992fec47cbac50629be8e3835b6f81328804b4662a4d6a94e60b65af`.
Only pinned `.olean`, `.olean.private`, `.olean.server`, `.ilean`, and `.ir`
objects were eligible. Executables and shared libraries were excluded.
Same-descriptor regular-file, identity, byte-count, and expected-hash checks
preceded advice.

Each of the two existing idle before/after verification phases successfully
advised all 12,594 distinct pinned objects: 25,188 calls in total, zero errors.
No separate extra advice pass was added. Successful advice does not establish
reclamation, and the accounting measurements showed no net reduction:

| Phase | Visible current before | Visible current after | Before minus after |
| --- | ---: | ---: | ---: |
| Before verification: toolchain segment | 13,474,430,976 | 13,489,631,232 | -15,200,256 |
| After verification: toolchain segment | 13,473,566,720 | 13,486,620,672 | -13,053,952 |

| Phase | Anonymous delta | File delta | Kernel delta |
| --- | ---: | ---: | ---: |
| Before toolchain segment | +9,170,944 | +5,795,840 | +159,744 |
| After toolchain segment | +7,356,416 | +5,795,840 | +126,976 |

These are observed accounting changes across the measured intervals; they are
not a unique causal attribution to advice. No speculative cache credit was
used at admission. At admission, visible `memory.max` was 17,179,869,184 bytes
and `memory.current` was 13,446,107,136 bytes. Its `anon`, `file`, and `kernel`
fields were respectively 185,085,952, 12,238,983,168, and 1,021,689,856 bytes.

The unchanged historical whitelist pass covered 407 files / 183,081,165 bytes,
between `16:36:57.049650` and `16:36:57.355814 UTC`, with an observed visible
current reduction of only 81,920 bytes. Five newly completed files also have
preserved housekeeping hash/identity receipts.

## Preserved evidence and limitations

The 66,985-row input inventories before and after are byte-identical, SHA256
`e59838ddb9d9f126857d2f8892c8f359ea157d6bd589b6727abedcb6664d4cae`.
The original inventories and advice JSONL files are retained. For readable
review, `chunks/manifest.json` lists 459 ordered chunks and reconstruction
hashes for five large evidence streams. Concatenate each listed part's bytes
without separators. One input export reconstructs both identical inventories.

The frozen proof source, toolchain, nine dependency pins, previous proofs,
partials, failed attempts and earlier evidence remain unchanged. Historical
dependency cache archive authentication remains incomplete, and visible cgroup
accounting retains the qualification `PARTIAL_VISIBLE_ANCESTORS; unseen limits
UNKNOWN`. This is neither a clean rebuild nor proof acceptance.

The earlier syscall diagnostic remains preserved at commit
`c3e356afbc8aa38d57fa4849515155d88f84a6a1`, path
`checkpoints/light-eft-finitelaw-failed-syscalls-20261017/evidence/compile/syscalls.trace`,
96,504 bytes, SHA256
`bdfea71a593885b885c87857c38db7f8bb5cdb364caf83df7aefa5c67cfbb37b`.
No trace was repeated for this attempt. The prior RSS-stop telemetry gap remains
a historical qualification; the new fixture tests do not retroactively close it.

`verify_publication.py` reconciles this publication without invoking Lean or
rerunning the attempt. `PUBLICATION.json` binds the result commit and scope;
`evidence-sha256.json` hashes every published checkpoint file except itself.
Python bytecode caches are excluded from publication; raw diagnostics are not.

The initial publication whitespace check stopped before a commit because the
preserved `approved-changes.diff` contains diff-context lines ending in spaces.
That raw patch is retained byte-for-byte. `publication-checks.json` records the
diagnostic and the successful whitespace check excluding only that evidence
artifact; no proof execution or source repair was involved.

## Reporting correction

An intervening terminal response incorrectly reported an unrelated October 16
SCC checkpoint. It is withdrawn as a result of this FiniteLaw delegation. On
resumption, the visible request concerned SCC work while the retained summary
described this FiniteLaw attempt; the worker followed the SCC request and
returned the wrong result for the delegation. The available evidence does not
establish why those contexts diverged. The subsequent read-only reconciliation
confirmed this attempt's admission refusal and that publication had not yet
occurred. This checkpoint publishes that correction together with the original
FiniteLaw evidence. It performs no SCC work and makes no SCC acceptance claim.

Publication ends with no Lean/checker process running and the common exclusive
lock free. No further resource experiment, proof execution, CI, website change,
or whole-paper completion is authorized or claimed by this checkpoint.
