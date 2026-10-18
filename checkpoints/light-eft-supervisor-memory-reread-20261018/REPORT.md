# Light EFT supervisor memory-field reread repair — fixtures only

Base evidence commit: `95b0256dfdf05bf415248c764510701f1b7d5dfc`.
Frozen Lean source remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`.
This additive checkpoint proposes a supervisor repair and records harmless fixture validation only. Independent read-only review is required before any production continuation. No Lean compiler, checker, resolver, cache advice, default Lake build, production batch, CI, or full frozen-input pass ran in this task. No Lean proof source, dependency pin, website, or prior checkpoint was modified.

The user reports independent acceptance of 45 new ordinary chains at the base commit, bringing the accepted total to 416, and acceptance of the CorePartitionBudget compile and exact resolution. That review is recorded as source/log/hash reconciliation, not fresh execution. Its replay remains rejected despite exit zero. This checkpoint does not qualify that replay or add a mathematical acceptance claim.

## Patch and scope

[supervisor-repair.patch](supervisor-repair.patch) contains the complete changes from the accepted baseline controls. Proposed `exit_transition.py` and `decision_telemetry.py` are new checkpoint copies; historical controls and raw evidence remain unchanged.

For an identity-validated row with only the expected missing VmRSS/VmSize errors and without positive no-mm exit evidence, the classifier now makes one immediate fresh stat/status capture before rejection. A per-TID, per-decision budget is shared with the existing FD-transition reread: the fresh row cannot request a second read. Both complete or partial captures, raw stat/status, original and fresh timestamps, and the reread reason remain in the sample. Policy classification uses the replacement effective row, never the stale row.

A fresh healthy live row receives ordinary memory policy checks and inherited-lock verification, including when another live row already supplied shared-mm telemetry. Positive exiting/no-mm rows use the existing fixed one-second grace; neither a zombie leader nor missing fields confirms whole-process completion. A fresh owned-sibling disappearance requires ENOENT proc reads and a separate positive disappearance check against the retained identity catalog. Malformed/access-error fresh captures, identity/start-time/Tgid mismatches, persistent live missing fields and live lock loss fail closed. The FD-transition path also consumes the same single-reread budget.

Earlier identity-valid RSS observations are retained for the maximum even if VmSize was absent or a fresh RSS is lower. RSS is never summed across TIDs. The shared-mm sample and effective classification may use the fresh row while the observed maximum still names an earlier capture.

The former broad policy filter is replaced by an index-and-error binding to the exact error objects contributed by the original leader to `collect()`'s flat error list. Only those specifically superseded original-leader memory-field errors may be resolved. Raw errors remain unchanged. Equal-looking unrelated VmRSS errors, accounting failures, parser errors and supervision errors are not suppressed.

`unchanged-controls.json` binds byte-identical `child_runner.py`, `pilot_child.py`, `pilot_accounting.py`, `shared_preservation.py`, both retained fixture scripts, and the existing lifecycle module. Resource gates, process limits, deadlines, accounting and owned wait4/status-matching code are unchanged. Limits remain AS 12 GiB, CPU 60 s, wall 90 s, file size 16 MiB and core zero; runtime visible/host floor 1 GiB, RSS stop 6 GiB and per-cgroup anonymous-growth stop 3 GiB. No production admission or memory-capacity claim follows from these synthetic fixtures.

## Final fixture results

All **44 final regressions passed** sequentially:

- 18 new deterministic memory-reread regressions;
- 14 retained whole-process lifecycle fixtures, copied byte-for-byte;
- 12 retained effective-reread lifecycle fixtures, copied byte-for-byte.

The new cases cover the exact saved CorePartitionBudget mixed snapshot with an exiting worker and with a fresh healthy worker; fresh healthy/exiting/gone responses; persistent missing telemetry; start-time/Tgid mismatches; malformed and access-error captures; initial malformed data without a reread; leader and sibling live lock loss; earlier RSS-limit retention; unrelated equal-looking memory errors and other collection errors; non-resetting grace expiry; and FD-first reread exhaustion. Saved historical fields are retained in `saved-mixed-snapshot.json`. Fixture identity remapping to the actual owned four-thread Python child is explicitly recorded; synthetic telemetry is not presented as a fresh production replay.

Exact sequential commands, options, raw output paths and exits are in [fixture-commands.json](fixture-commands.json). The final successful commands were:

```text
python3 -B -u checkpoints/light-eft-supervisor-memory-reread-20261018/test_memory_reread.py
python3 -B -u checkpoints/light-eft-supervisor-memory-reread-20261018/test_whole_process.py
python3 -B -u checkpoints/light-eft-supervisor-memory-reread-20261018/test_effective_reread.py
```

Every child is harmless Python/native-thread code, runs under the existing universal exclusive lease, inherits the same limit setup, and has its submitted source hash, harness hashes, actual PID and owned wait4 receipt. Original proc reads, synthetic overrides, fresh captures, sample classifications, FD checks and cleanup results are retained. All attempt IDs are unique, intervals and leases do not overlap, every direct child is reaped through the existing owned wait4, and every lease verifies kernel ECHILD before release. The common inode was never replaced or unlinked.

There are **66 retained fixture attempts** in total, including two failed fixture-setup attempts and repeated successful prefixes. Invocation 01 passed four cases before `fresh_gone` exposed a fixture mistake: the synthetic disappearance check was true before the initial row had been classified. Invocation 02 passed sixteen cases before `grace_expiry` exposed a mock recursion in fixture construction. The fixes deferred disappearance until the fresh capture and precomputed exiting rows outside the mock. Neither changed the supervisor patch. Both failures, tracebacks, receipts, captures, child source and exact earlier harness snapshots remain preserved. Invocation 03 passed all eighteen new cases. Expected supervisor rejections in negative fixtures count as fixture passes; eventual child exit zero never overrides those rejections. No Lean warning classification is applicable because no Lean ran; the two new failed-attempt diagnostics are fixture setup errors, not compiler warnings.

## Preservation and review boundary

[reconciliation.json](reconciliation.json) records the offline verification. All **417 objects and 346 resolutions** retain their original membership, identities, sizes and hashes, across 763 bound files. All **1,269** entries in the original batch evidence manifest still match. Its SHA256 is `ac46f94c36d0e47bd72b8037099ace3a7031bcbd455c1d8feaab8f97e9f76627`.

CorePartitionBudget remains **83,848 bytes**, SHA256 `1767dd8c642b0f2f8bf31119c76e9ce8a9a8464bd46eca8534175e2b21fcd233`. Original rejected replay attempt `0fd875cd7cf646acbb0b8453db16a991` remains `state=failed`, `exit=0`, with its untouched raw log, samples and receipt. The observed runnable worker TID275245 had nonzero stat memory but missing status VmRSS/VmSize; the original leader's nested reread was zombie/no-mm and two siblings were positively gone. The repair is tested against this snapshot, not retroactively applied to its acceptance status.

Prospective production work remains **206 stages**: CorePartitionBudget replay, 68 ordinary chains for entries 418–485, and the aggregate compile. None ran here. Production continuation requires independent review and a separate authorization; this checkpoint changes no production launch configuration.

Terminal reconciliation found no active compiler/checker/tracer and a free common lock at device **33**, inode **3849**. Resource observations are retained separately and do not substitute for admission checks. The checkpoint is published with CI skipped, then paused for independent review. No whole-paper completion is claimed.
