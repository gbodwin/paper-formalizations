# Supplied-forest one-shot attempt: stopped before Lean

Reviewed wrapper: **2aa4e6f531b7968a1f3dd820aa856b73c628d161**.
Staged mathematical draft: **40029953e9e53525f0f1f431d6d56333b05183a3**.
Accepted imported mathematical source: **78cb40c7837db049d645d73696f2e0b724ce8a3b**.

**The single authorized invocation failed during input binding, before new-lock creation and before any compiler/checker stage. No retry or policy/source repair was attempted.** The proof remains uncompiled. This is an incremental harness admission failure, not a mathematical counterexample, kernel rejection or theorem acceptance.

## Fresh coordination and capacity

[preflight.json](preflight.json) records no competing visible ordinary worker/compiler, approximately 4.64 GiB free disk, 15.26 GiB visible memory headroom and 16.76 GiB host MemAvailable. The existing bounded accounting qualification remains PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN. The common lock pathname was absent. No continuity with historical inode 33:3849 was assumed.

The user's explicit authorization of one sole-worker attempt and idle independent reviewer was bound into a fresh incarnation-specific [coordination document](coordination.json). The unchanged revised entry was called exactly once by [invoke_once.py](invoke_once.py), with an exclusive outer invocation claim. This thin caller did not change commands, guards, inputs, limits or wrapper code.

## First failure

The entry raised:

    contracts.Rejected: Unlisted effective search input

The exact stack and exit-1 result are preserved in [controller.log](controller.log) and [controller-result.json](controller-result.json). It failed in driver.make_production_plan at the requirement that every file enumerated below each dependency/object search root appear in the approved prior input inventory.

A read-only post-failure diagnostic found **73,846** unlisted files:

| Suffix | Count |
| --- | ---: |
| .hash | 53,484 |
| .sig | 11,426 |
| .trace | 8,926 |
| .a | 10 |

The first path enumerated by that diagnostic was /workspace/paper-formalizations/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.ilean.hash. The guard's original exception omitted the filename, so this is identified as the diagnostic's first path, not an additional fact in its original stack.

[unlisted-summary.json](unlisted-summary.json) gives per-root counts and all ten static archive entries. The complete [metadata list](unlisted-inputs.jsonl) and [ordered chunk manifest](unlisted-input-export/manifest.json) preserve every path and size, with verified reconstruction. The full pretty diagnostic is also retained. This enumeration is not a stage retry or an authenticated content inventory. No file was added to the input authority, suppressed, deleted or reclassified. In particular, static archive relevance is left for independent review.

The blocking issue is the mismatch between an all-files search-root enumeration and the earlier approved input inventory. Any correction to that boundary needs review; this attempt does not infer that all extras are semantically irrelevant.

## Terminal disposition

[terminal-state.json](terminal-state.json) records:

- zero Lean/compiler/checker invocations and zero stage receipts;
- no production evidence directory or core production invocation claim;
- no fresh work/output root or partial compiler object;
- no common-lock creation or acquisition;
- no active compiler/checker at terminal inspection.

The outer invocation claim and complete startup diagnostics are preserved. Whole-batch lease/owned-child cleanup were never entered because failure preceded lease creation; there is no ECHILD execution receipt to claim. No source was promoted, no full graph rebuild/replay was run, and there was no dependency retrieval, website change, clean-provenance claim or exact-commit CI result.

All approved wrapper/source/pin bytes and historical receipts remain unchanged. This additive failure-evidence checkpoint is published only on light-eft-spanners-checkpoints with [skip ci], followed by exact remote verification. The worker is idle for independent result review.
