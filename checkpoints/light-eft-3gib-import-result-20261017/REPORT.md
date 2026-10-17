# One 3 GiB bounded tiny import: passed

**BOUNDED_IMPORT_LOAD_PASSED.** Exactly one authorized invocation and one Lean child, exit **0**, with an empty raw diagnostic log. No retry or additional compilation. This establishes only bounded loading of the original tiny import; it does not establish a full clean build, proof replay, heavier-module capacity, archive authentication, CI readiness or whole-paper completion.

Frozen production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`. The user reported independent approval of allocator evidence `235cbab5db150b0eaad83c16d233ee5813d41aa2`; this records that authorization, not a fresh independent review.

## Exact source and command

Attempt `a66d375fee4d45c09bafd80b4bf82800`, child PID 153318, created 2026-10-17T14:14:25.376825+00:00, finalized 2026-10-17T14:15:27.414041+00:00. Those times include preflight and preservation hashing; the child's wall deadline remained 90 seconds.

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true /workspace/light-eft-verification/.lake/bounded-import-20261017-9675cd8d185f45a7ab9d014bc8f19fdd/ImportSmoke.lean
```

The 27-byte submitted source is `import Aesop.Script.Tactic` followed by a real newline. SHA256 `77bfe1bd222bea9c18d7450f1f5b3b3fd0195f4f107b83fd39f98dddf605ab19`; exact hex `696d706f7274204165736f702e5363726970742e5461637469630a`. The official executable SHA256 remains `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` (Lean 4.34.0). The original explicit import environment was restored: LANG, LC_ALL, LEAN_SYSROOT, LEAN_PATH and LEAN_SRC_PATH only. No MIMALLOC_VERBOSE, allocator tuning, runtime shim or project object was introduced.

**Progress-report correction:** an intermediate assistant update misread the escaped display of the source bytes and incorrectly suggested a literal backslash-n defect. A byte-level check shows final byte decimal 10/hex 0a, and the import succeeded. The source was never changed. That mistaken interpretation is preserved here rather than silently omitted.

## Narrow authorized changes and enforcement

[approved-changes.diff](approved-changes.diff) records changes against the previous stack64 import runner. Fresh fixed path suffix: `9675cd8d185f45a7ab9d014bc8f19fdd`. The child AS soft and hard limits are both **3,221,225,472 bytes**, independently verified by parent kernel prlimit readback before exec. CPU remains 60 seconds, wall deadline 90 seconds, FSIZE 16 MiB, CORE 0, and monitored stop floor 512 MiB. Existing `-j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true` options are unchanged.

Both visible cgroup headroom and host MemAvailable must be at least **3,758,096,384 bytes** after hash/advice preflight. This was additionally rechecked immediately before exec:

| Observation | Visible headroom | Host MemAvailable |
| --- | ---: | ---: |
| After preflight | 4131082240 | 17680433152 |
| Verified pre-exec | 4126556160 | 17680781312 |

The existing identity-checked cgroup monitor was extended with pids.current/max/events. It rejects observed PID exhaustion, changed limits/events, OOM changes or the memory stop floor. Before/after observations include inherited NPROC/STACK and memory.stat. The wrapper itself is included in submitted-input hashes. Hash/advice logic and fail-stop cleanup are unchanged; there is no fallback or automatic cap increase.

The prior diagnostic directly logged a 1 GiB mimalloc arena. Together with the reviewer-supplied early stack finding this motivated the authorized cap change. The successful attempt does not independently prove the unique cause of prior failures or measure the early thread's stack reservation.

## Resource observations and classification

Zero bytes of compiler diagnostics: no reported Lean errors or warnings. The actual child exit is 0. wait4 maximum RSS: **311164 KiB**, including the launcher/payload lifetime. Sampled maxima: RSS **276840448 bytes**, VM **3170095104 bytes**. The 250 ms samples are not continuous peaks. The sampled VM is close to the AS cap; do not infer larger-import capacity from this result.

Before/after same-real-UID threads: 240. Both visible cgroups pids.current: 262, pids.max: literal `max`, pids.events: `max 0`, unchanged. RLIMIT_NPROC: 71955/71955; inherited RLIMIT_STACK: 8388608/unlimited, unchanged. Parent OOM/kill/group counters stayed 1/1/0 and child-group counters stayed 0/1/0. Hidden ancestor limits remain unknown. Raw monitoring and before/after observations are preserved.

## Preservation, evidence and terminal state

All 66,978 input rows were preserved; before/after inventories are byte-identical, SHA256 `cd86c88cbefc24fdd9e5b81f6ae7a7556c3e4d7e440b7b0e8315acdbfc3abe41`. [386 ordered chunks](chunks/manifest.json) reconstruct inventories and advice logs; all raw originals remain. Prior sources, pins, partials, failed attempts, allocator diagnostic and reporting corrections are unchanged.

The receipt confirms direct child reaped, all descendants gone, kernel ECHILD verified and input preservation verified. Universal lock device 33/inode 3849 was held through cleanup/preservation and is now free. No Lean/Lake/checker/extractor process remains. Both fixed directories and the wrapper's one-use marker are consumed. No retry, CI dispatch or subsequent proof work was performed. A previously generated untracked scripts/__pycache__ directory was left untouched.

Publish with CI skipped and pause for independent review. This is bounded import success only.
