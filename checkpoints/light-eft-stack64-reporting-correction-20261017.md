# Reporting correction: completed Light EFT stack64 pilot

Recorded 2026-10-17T14:02:59.894965+00:00.

The intervening assistant response incorrectly reported an unrelated, already-completed SCC checkpoint instead of the assigned Light EFT pilot. During that detour, only read-only repository, evidence-hash, resource and lock checks were performed; no SCC source was modified and no compiler was invoked. The SCC response does not describe the Light EFT experiment and must not be used as its outcome.

Inspection of actual preserved Light EFT paths confirms the approved single `-s65536` pilot had already run, not been refused or left unstarted. Attempt `34e112168e9944888c7fbc78040eef32`, child PID 152148, exited -6 (SIGABRT) with `failed to create thread: Resource temporarily unavailable`. Exact cause remains undetermined. All caps/gates were unchanged; before/after PID observations showed no visible exhaustion. Cleanup and input-preservation checks passed. No import success is established.

Result commit: `2be240c6a839ba310a52249a40cca1ded27b038e`.
Evidence commit: `0e2fc0d91ecd7babe19d560ad92efe61b89dec5c`.
Frozen production: `78cb40c7837db049d645d73696f2e0b724ce8a3b`.

This correction verified all 408 entries in the existing evidence manifest and confirmed the remote branch already pointed to the evidence commit. The common lock inode 3849 was available; no Lean/Lake/checker/extractor process was active. This was read-only evidence reconciliation, not fresh execution. No duplicate pilot, retry, cap increase, CI dispatch, source modification or whole-paper completion claim occurred. Existing evidence is preserved unchanged.

[Preserved report](light-eft-stack64-import-result-20261017/REPORT.md)
