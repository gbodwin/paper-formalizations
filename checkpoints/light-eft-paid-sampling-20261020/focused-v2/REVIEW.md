# Reviewed source fix and focused validation plan v2

The parent independently reviewed source-only checkpoint1cd3bbf8, its16 payloads
and13 additive files, and confirmed the intended3L+2 and5L+5 supplied-response
transition bounds. Its one requested proof correction is applied exactly:
`simp only [List.append_nil] at hs` immediately after `collect_trace` creates hs,
before composing hs.trans hr. This aligns the intermediate reverse state; the
later simpa cannot perform that alignment before trans is elaborated.

No other Lean source or fixture byte changed. Both staged modules and all eight
equation fixtures remain uncompiled. This is reviewed source, not Lean acceptance.

DEPENDENCIES-16.json binds the exact transitive existing project-source closure,
all16 current source byte hashes, and16 preserved object carriers. Source bytes
match accepted a04960a8 and the preserved chain-index source associations; local
object bytes match those indexed objects. Only byte association was checked.
No old compile/resolution/replay/audit was rerun, and no historical absolute path,
runtime namespace or inode was restored. The copied carriers are at the freshly
named input root recorded in the plan. Clean dependency provenance is not claimed.
External Mathlib/Aesop object closure and supported parts still require fresh
admission; the plan does not pretend those inputs already exist.

FOCUSED-PLAN.json is a non-executable bound review plan. One physical output root,
/workspace/light-eft-paid-focused-v2-20261020/work/objects, serves both new modules
under the single LightEFTPaidSamplingStage package marker. No separate per-module
root is permitted: Lean's first-package selection must find both modules in that
same package. The output/work root remains absent; no compiler has been launched.

The finite order is compile/resolve/replay/audit for serialization, then the same
four operations for composition, followed by elaboration of the eight fixtures
without generating another object. Each first-module compile part is recorded in
an immutable completed-output ledger at its original path, byte hash, length and
identity. That ledger must remain present before, during and after every second-
module operation. Later guards must allow exactly the frozen first-module parts
plus the current finite target parts, protecting the former from mutation. They
must not demand an empty root or allow arbitrary old files. Only the exact second
target's compiler temporary is permitted, and only under the unchanged verified
exec/PID authority. Both ledgers remain protected during fixture elaboration.
Completed resolver, audit, receipt and evidence outputs are also immutable.

The current single-target production output guard cannot be reused unchanged for
the second compile: it would reject the first module as an unexpected file.
An explicit finite shared-package ledger adapter and exact resolver/audit helpers
must be implemented and independently reviewed before execution. This is an open
implementation prerequisite, not implicit execution authority in this plan.

The plan binds source hashes, observed tool binaries and the unchanged Lean flags,
3/3/4/4GiB admission, CPU60 except audit90, wall90, prespawn300, AS12GiB, RSS6GiB,
anonymous-growth3GiB, stop-headroom1GiB and existing PID/OOM/output/lease/owned-
cleanup controls. check_plan.py verifies current byte bindings, the16-module
scope, shared root, first-object ledger preservation, finite commands/output
authority and reviewed proof fix. Ledger keys use exact fully qualified producing
stage IDs, and each protected ledger must refer to an earlier actual stage.
Its valid plan passed and11 negative plan
mutations were rejected. These are read-only Python plan checks, not the eight
Lean fixtures, a kernel audit, or a process-lifecycle test.

Restoring the selected environment did not qualify it. A fresh read-only snapshot
still reports non-initial cgroup namespace inode4026532205 and truncated/.. mount.
Full-hierarchy discovery refuses hidden ancestor limits. The preserved partial-
visible profile also observed only173711360 bytes headroom, below the unchanged
3/4GiB floors, with unseen limits UNKNOWN. The initial namespace was not made
available through the existing unprivileged view; /proc/1/ns/cgroup inspection was
kernel permission-denied. There is no exposed alternate execution environment.
No namespace entry, remount, threshold relaxation, fallback runner, cache eviction
or privilege bypass was attempted. No failed startup/Lean launch was repeated.
FRESH-ACCOUNTING.json retains the current raw/partial observation.

The local source worktree and original1cd3bbf8 checkpoint are preserved. Remote
integration remains a04960a8; all five nonterminal CI queries returned zero. Fast
mode remains off, only this ordinary worker is active in this thread tree, and no
local compiler is active. No source push/CI trigger or repeat accepted decoder/
corollary validation occurred. Whole paper remains open. A qualifying execution
context, admitted dependency closure and reviewed finite adapter are required
before running this plan; future fresh contexts must rebind paths/identities.

The earlier README/SOURCE-CHECKPOINT files remain historical v1 evidence. This
supplement and FOCUSED-PLAN source hashes bind the corrected source. This transport
inventory must not be used as a production manifest.
