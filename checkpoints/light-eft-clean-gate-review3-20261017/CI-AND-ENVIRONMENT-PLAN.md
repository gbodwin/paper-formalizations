# Environment and CI inventory — read-only, no installation or dispatch

## Existing execution environments

The selected ordinary execution connection exposes `/workspace` and the current Linux host. The new raw observation in `evidence/terminal-environment.json` records its cgroup namespace, mount data and refusal. It is a **non-initial cgroup namespace**, which this deliberately conservative gate does not support. Waiting for memory to change cannot make this namespace qualify.

Tool discovery exposes exec/write-stdin and a wait tool for an already selected starting environment. It exposes no ordinary Codex environment registry, list or selection operation. The only environment-list tools found are explicitly restricted to Codex Security tasks; those were not invoked for a Lean task. No alternate workspace, canceled workspace, SCC source, host namespace, new VM or container was opened or created. Other directories in the filesystem do not establish separate qualifying environments.

`ubuntu-latest` in the proposed workflow denotes a future hosted allocation, not an existing inspected qualifying runner. No runner was allocated and no GitHub runner inventory authority is exposed by the permitted connector. A qualifying existing ordinary environment has therefore **not** been verified. The exact access gap is an ordinary-environment inventory/selection capability or an independently supplied verified environment observation, not an implementation question for Greg. The current connection remains useful for preparation only.

## Repository trigger/ref inventory

Read-only GitHub reads enumerated **154 current branches at 152 distinct commit tips**, and fetched only `.github/workflows` directory metadata and workflow definitions at those exact tips. The 117 distinct workflow blobs were deduplicated and their returned bytes checked against their Git blob hashes. No proof sources from other papers were opened. Raw definitions and branch mappings are retained; `evidence/ci-ref-inventory.json` includes literal event filters and concurrency fields.

**153 of 154 branch tips contain at least one workflow lacking the exact shared workflow-level group and `cancel-in-progress: false`.** These are conservatively marked potentially ungrouped; the report does not assert every push/PR filter matches every branch. The checkpoint branch alone has exclusively shared-group workflow definitions in this inventory. Main remains ungrouped. A main-only change cannot constrain workflow definitions retained on other refs.

The open-PR read returned none. The run collection reported 533 historical runs; the 100 returned recent records are retained with event/ref/commit/path/run-attempt identities. Historical reruns use prior definitions and are not retroactively repaired by changing current branch tips. No claim of a complete 533-run audit is made. The tag-list endpoint was rejected by the connector (`INVALID_ARGUMENT`); no alternative was used to bypass that restriction. Thus tags and the full historical-rerun surface remain explicit inventory gaps. The workflow-collection endpoint restriction recorded previously also remains.

## Bounded installation proposal and unresolved exclusion authority

The earlier two-file proposal is preserved unchanged as a proposal: add only the shared concurrency block to the exact observed main `lean.yml`, and install only the dispatch-only Light EFT workflow. Never merge a checkpoint branch wholesale. The eventual template guard must contain production `78cb40c7837db049d645d73696f2e0b724ce8a3b` and the full subsequently reviewed harness commit; checkout refs and dispatch inputs must exactly match. No install is permitted by this preparation.

This alone is **not a safe dispatch route**. A bounded safe route requires all of these conditions before any later execution:

1. Independently approve the harness and authenticated dependency artifact; verify an actual qualifying runner/accounting view.
2. Obtain an explicit repository-wide CI reservation from an authority able to coordinate every workflow initiator, including pushes, PR-related events, schedules, dispatches and historical reruns. A queue snapshot is not such a reservation. No unrelated workflow is silently disabled, no security permission is broadened, and no old branch is rewritten by this plan.
3. Under that reservation, refresh branch/tag/run/trigger inventory through permitted reads, establish that no ungrouped producer can start during the reserved gate, and drain preexisting running/queued work. If that exclusion cannot be established, do not install or dispatch. Current tools/authority do not establish it.
4. If separately authorized, apply just the reviewed two-file workflow change to the fresh default-branch tip with CI skipped, verify the resulting definition and exact frozen refs, then dispatch once inside the established reservation. Preserve all receipts and artifacts and release the reservation only after the job and all processes have ended.

For a technically enforced route without a coordinated reservation, a repository-wide admission mechanism covering stale refs and reruns would be necessary. GitHub workflow concurrency is opt-in per definition; adding the group only on main is not that mechanism. No such mechanism or authority is available or proposed as a silent settings change. Patching all stale refs would still leave historical reruns and would exceed this narrow installation scope.

**Current conclusion:** no fully established safe CI route or qualifying execution environment is available from these permissions. The deliverable is the bounded conditional installation plan and the exact remaining authority/access gaps. No CI, default-branch write, installation, cancellation or dispatch occurred.
