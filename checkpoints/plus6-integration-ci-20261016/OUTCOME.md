# CI outcome: PASS, artifact reconciliation pending independent reviewer

The single exact-source gate completed **successfully on its first attempt**.

| Item | Exact identity |
| --- | --- |
| Tested immutable source | `c189a4e93786b47c7dbc23146c6b44a5b9cc75dc` |
| Preparation commit | `0228d038b644fab667e61a17f647cfb139b09e3e` |
| Trigger commit | `3e3e887c39eb3905ccb7db68c5ea81560e627912` |
| Run | [38828357360](https://github.com/gbodwin/paper-formalizations/actions/runs/38828357360) |
| Single verify job | `116741040644` |
| Artifact | [12016601601](https://github.com/gbodwin/paper-formalizations/actions/runs/38828357360/artifacts/12016601601) |
| Artifact size | 988,665 bytes |
| GitHub-reported ZIP SHA256 | `908dbe2c4f36fffdcda8991980ed4196114730813067b8ffcf4714bc05b5fc67` |
| Started | 2026-10-16 00:14:37 UTC |
| Terminal success reported | 2026-10-16 00:24:59 UTC |

The old conditional source pin is not used as integration evidence. The integration source was separately checked out by immutable commit in a clean directory. The runner enforced the official archive digest and toolchain version, the immutable manifest hash, and all nine dependency revisions; it downloaded the official mathlib cache normally. No local compiler/checker ran during CI, no parallel worker was spawned, and the CI job has no matrix.

The retrieved full decoded [job log](monitoring/job.log) reconciles **117 commands, all exit 0**, including **39 source compilations** and **38 individual leaf kernel replays**. The source-derived inventory is 36 library modules, two imported support leaves, and one aggregate. The additional two leaves are not audit scripts. The 23 inherited modules must match the exact previously reviewed 36-warning diagnostic baseline. The other 15 modules plus aggregate are strict, warning-as-error compilations. The combined recursive audit must pass 373 actual-owner roots, 19,646 constants, 14 opaque bodies, and only `propext`, `Classical.choice`, `Quot.sound`; the gate's successful exit confirms these assertions. The artifact contains their raw individual logs, exact commands, source/object hashes, and recursive audit rows.

The workflow wrapper emits one separate runner warning about pinned checkout/upload actions targeting Node.js 20 while GitHub forces Node.js 24. This is a runner/action deprecation warning, not a Lean warning; it did not fail either action. The 36 inherited Lean warning count remains distinct.

## Evidence access limitation

The GitHub connector returned the ZIP as reusable file reference `file_00000000e77081fd9d2916b9b46c1e77`. Reading its signed content URL from the selected execution environment returned **HTTP 403**. No credentials, security settings, or network rules were changed and no bypass was attempted. The ZIP bytes were therefore **not independently hashed or extracted here**. The SHA256 above is explicitly GitHub's artifact metadata/upload receipt, corroborated in the full job log, not a local digest calculation.

The [artifact metadata](monitoring/artifacts.json), [terminal run response](monitoring/run.json), [job/step response](monitoring/jobs.json), and [log reconciliation](monitoring/log-reconciliation.json) are preserved. The artifact remains available through its GitHub run link for the independent reviewer. `reconcile_artifact.py` is a prepared read-only artifact checker; it was not run because the ZIP bytes are unavailable here. After downloading and verifying the ZIP SHA256, extract it and run:

```text
python3 checkpoints/plus6-integration-ci-20261016/reconcile_artifact.py <extracted-evidence-directory> <output-json>
```

This verifies every artifact evidence-manifest hash and the result/command/replay/warning/audit counts without invoking Lean. The independent reviewer should also reconcile source/object hashes and statement fidelity. This outcome does not claim that independent artifact review has already happened.

## Failures and final idle status

There were no CI compile/checker failures or reruns. The earlier direct shell API read returned HTTP 403; the authorized connector provided all status reads. A running-job log read returned `BlobNotFound` before logs finalized, then succeeded after completion. The signed artifact content download returned HTTP 403. These diagnostics are retained or described; none is reclassified as a proof failure. The initial nonexistent remote-tracking-ref lookup is documented in the preparation README.

Before trigger, all five repository active/queued states were zero and local compiler/checker processes were absent. The runner's preflight succeeded. The unrelated general Lean workflow [38828357359](https://github.com/gbodwin/paper-formalizations/actions/runs/38828357359) was skipped, so no multi-paper compiler job ran. After terminal success, all five repository states are again zero and local compiler/checker processes remain absent; see the terminal idle receipts. The certified checkout is clean and unchanged.

Remaining agreed scope is reconciled in [REMAINING_SCOPE.md](REMAINING_SCOPE.md): directed/weighted distance-preserver and directed reachability applications remain beyond the current spanner results. Algorithmic runtime, optional graph-model/constant improvements, the retracted all-pairs claim, and website publication are not added to this task. This is bounded integrated +6 existence validation, not whole-paper completion.
