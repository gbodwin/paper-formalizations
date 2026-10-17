# Third-review fixes — Light EFT preparation only

The reviewer accepted preservation/hash evidence `64ddfd9fa9d27f742a3b469cc53fbbef8ec98897` and rejected prepared harness `f4bc68fd81ee49322e2dd9342ba80188741eda81` as finished. This additive checkpoint addresses the three concrete findings. It is unreviewed preparation; no Lean, leanchecker, Lake, native extractor, CI, installation or dispatch ran. Frozen production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`. All prior evidence is preserved.

## Cgroup corrections

The code no longer requests `cgroup.type` from the genuine hierarchy root. A realistic fixture supplies root `cgroup.controllers` but no root type file and checks the exact read list. Initial cgroup namespace identity and a visible full hierarchy remain required; the root exemption does not turn missing non-root memory counters into unlimited budgets.

Discovery now parses all mount types, mount IDs and mount-parent IDs. For each controller/accounting file, only the selected full cgroup mount and its mount-parent chain may cover the path. Any other covering mount refuses admission, including a same-device leaf/ancestor cgroup bind, a tmpfs/non-cgroup mount, a file bind, a stacked mount at the selected root, and an overmount above the selected mountpoint which hides its parent chain. An unrelated `/bound` sibling remains irrelevant. The code rejects duplicate mount IDs, cycles and ambiguous hierarchy mappings. It still verifies membership and mountinfo stability and all applicable ancestor `memory.max`/`memory.current` values, with the unchanged 4 GiB system/effective-cgroup requirement.

## Cleanup exclusion and failure semantics

Non-ESRCH discovery/signaling failures are no longer allowed to unwind cleanup. Cleanup records the error and retries while retaining the lock. An outer fail-stop barrier covers unexpected cleanup-helper errors, signal setup, subreaper restoration and receipt/log finalization. Receipt-persistence errors are recorded in memory and reported to stderr where possible, and finalization retries; they do not authorize releasing exclusion with an unknown descendant state.

Before release, the direct child must be reaped, the descendant scan must be empty, and a kernel `waitpid(-1, WNOHANG)` must report ECHILD while the supervisor is still a subreaper. The previous subreaper state is then restored, diagnostics finalized, and signal handlers restored. No retry limit converts an unknown outcome into success. A persistent cleanup failure remains stopped with the lock held; recovery still records FAILED and raises, rather than printing a successful gate marker. Involuntary SIGKILL/host loss cannot be made recoverable by Python; the inherited lock and preserved pre-spawn receipts remain, and such an interrupted run cannot be accepted.

Harmless fault-injection tests inject repeated proc-discovery failure, non-ESRCH signaling failure, subreaper-restoration failure, receipt-finalization fsync failure and an unexpected cleanup-helper exception. Every injection explicitly tests that a second open cannot acquire the lock. After recovery, tests require FAILED state, raw error records, direct-child reaping, no descendants, kernel ECHILD confirmation, restored subreaper state, and a free lock. The synthetic children are Python only; memory admission and executable validation are mocked only inside tests. They are not Lean execution receipts or evidence that this host meets admission.

## Tests and preserved evidence

The final new suite has **12 tests**, and both prior suites pass (**20 + 7**), for 39 distinct tests in the final runs. The first raw review-3 test log also contains nine imported existing cgroup tests; those duplicate executions are preserved but are not counted again as new tests. All logs, fault events, submitted harmless source snapshots and exported UUID receipts remain in `evidence`. Intentional fault cases return failed supervisor attempts as expected; no compiler ran. Earlier test fixtures and evidence are not rewritten.

The accepted exhaustive audit and official singleton resolver are unchanged. All 486 source hashes and package pins are reconciled against the frozen source plan. The future gate still requires 486 fresh strict builds, 485 singleton replays (each with an official resolver), one audit and version admission: 1458 Lean/checker invocations, all serial, none executed here. `EXACT_SOURCE_PASS` remains after successful finalization only. The dependency artifact status remains unavailable; no Cache.Main/native/build fallback exists.

## Plans, inventories and exact blockers

- [Dependency artifact provenance plan](ARTIFACT-PROVENANCE-PLAN.md) specifies the pinned module-to-official-archive mapping, authenticated archive hashes, independently verified unmodified extractor, exact command/stdin, archive-to-file mapping, toolchain/pins/full inventory and bundle identity. The installed extractor was hashed read-only, not executed. The required authenticated artifact/provenance is still absent.
- [Environment and CI plan](CI-AND-ENVIRONMENT-PLAN.md) records the permitted tool inventory, unsupported current namespace, 154-branch/117-workflow-blob inventory, 153 potentially ungrouped branch tips, denied tag read and historical-rerun gap. No other ordinary environment can be inventoried/selected through the exposed tools. Waiting on this namespace is not a solution.
- No safe CI route is claimed. A two-file main install cannot govern stale-ref definitions or old reruns. A coordinated repository-wide reservation with verified exclusion, or a separately authorized comprehensive admission mechanism, remains necessary. Neither has been established; no unrelated workflow is disabled and no permissions are broadened.

No production proof or website changed. Theorem 34's general lower claim remains open, modeled runtime limitations remain explicit, and this work does not claim whole-paper completion. Publish additively with CI skipped and stop for independent code review.
