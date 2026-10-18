# Fresh exclusive ownership proposal — disabled this turn

The universal pathname remains /tmp/distance-sparsification-single-compiler.lock. **No file was created, opened for acquisition, locked or replaced in this preparation.** The historical (device 33, inode 3849) receipt is retained as historical evidence only.

## What the current read-only observations establish

environment.json captures process identities, readable FD observations, visible kernel locks, observer namespaces and identity-checked visible cgroup accounting. No separate ordinary worker or Lean/Lake/checker/leantar process was visible. No readable FD names the common lock, including an unlinked instance. Four process FD directories were inaccessible; PID1 mount/PID namespace links were permission denied. These observations do not certify inaccessible namespaces or remote workers.

Current PID1 began at 2026-10-18T10:43:00.420000+00:00, after the preserved audit's 04:08:26 UTC receipt. Its old supervisor/child PIDs are absent. Thus the old process/ownership epoch is not continuous with the current visible process tree. The lock is absent even though the current /tmp device is still 33. The visible cgroup namespace text matches the old receipt; that alone cannot prove process, mount or lock continuity. Historical mount/boot identity was not established for comparison. Sandbox observer mount namespaces are not a substitute for coordinator confirmation of the shared underlying /tmp.

All 486 accepted source hashes still match. The 196 LightEFT objects in this draft's transitive LightEFT import closure were read and rehashed against the accepted audit input inventory. Their bytes remain available; this is not a new kernel execution.

## Existing implementation constraints

- scripts/LightEFTExactSupervisor.py and scripts/LightEFTSequential.py use this pathname but open with a+; even a no-child admission would create it. Neither was invoked.
- The older ExactSupervisor memory helper demands full initial-cgroup visibility. The subsequently reviewed finite-chain/audit guards instead retain the bounded PARTIAL_VISIBLE_ANCESTORS qualification. Do not silently fall back between these policies.
- checkpoints/light-eft-audit-adapter-review-20261018/shared_preservation.py, Lease, opens r+ and requires exactly 33:3849. The clean-context validators also hard-code that historical tuple. Their old scope/identity assertions must not be bypassed or overwritten.
- The reviewed finite-chain pilot pins FiniteLaw, a previous output root and its old execution scope. It is not an authorized runner for this new module. A separately reviewed, narrow adapter is needed, retaining its limits, accounting/handshake, PID-incarnation checks, raw telemetry and fail-stop descendant reaping.

No supervisor or preserved evidence is modified here. supervisor-bindings.json identifies the actual implementations inspected.

## Proposed recovery sequence, only after independent review

1. The coordinator confirms the sole ordinary worker, idle reviewer, no competing compiler/checker and the exact selected environment. All possible launchers must agree on the same underlying lock directory and new ownership epoch. If this cannot be established, stop; absence of a pathname alone is insufficient.
2. Reinspect the complete visible process tree, readable descriptors and kernel lock table. Preserve permission/visibility limitations. Refuse active worker/compiler, unexpected existing lock, changed namespace/mount mapping, or unexplained open/deleted common-lock descriptor. Do not revive, kill or inspect deleted workspaces.
3. Under that coordinated exclusion, open a directory FD for the trusted common /tmp and record its identity/mount. If the pathname remains absent, a newly reviewed owner may atomically create it with openat(O_RDWR|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC, 0600), then acquire flock(LOCK_EX|LOCK_NB). This is a proposal, not an executed command. EEXIST or contention means stop and reconcile, with no unlink/replacement and no automatic adoption.
4. Require a regular singly linked file owned by the expected execution user. Compare fstat of the owned FD with no-follow stat at the pathname, and record the new device/inode, FD mount identity, boot/process namespace observations, supervisor PID/start time and lease UUID. Persist the new epoch receipt. Never infer historical continuity, even if a numeric identity happens to match an old one. Keep the file permanently; never truncate, unlink or replace it.
5. Keep that one open-file description and exclusive lease through the entire four-stage batch. Recheck FD/path identity at every admission, before each exec acknowledgement and before release. Each child inherits this same FD; its pre-exec handshake must match the parent's current identity and live child incarnation, limits, SID/PGID and recorded command/source hashes. No separate per-stage open/lock or explicit unlock of a shared child description.
6. Perform fresh source/object/pin/tool binding and admission under the lease. Use the reviewed visible-accounting identities and bounds stated in execution-proposal.json; unseen ancestors remain UNKNOWN. No cache advice, network access, extraction, clean executor, or implicit dependency build is proposed.
7. A first failure stops the batch. Signal/reap the direct process group and adopted descendants with the reviewed fail-stop lifecycle barrier. Retain the lease while outcome is unknown; require wait4/PID-incarnation evidence and final kernel ECHILD before closing it. Preserve every UUID receipt, submitted-source snapshot, raw diagnostic, runtime sample and partial object, including failed attempts. No automatic retries or promotion.
8. After the final no-child/resource/identity checks, close the owner's FD to release the lease, leaving the inode present, and pause for independent review.

This sequence still requires approval of the new epoch and a scope-specific bounded wrapper. The existing whole clean executor remains disabled; no source/toolchain authentication, clean build, fresh acceptance or cross-environment exclusion is inferred from this proposal.
