# Light EFT clean exact-source gate — preparation only

Production source is frozen at `78cb40c7837db049d645d73696f2e0b724ce8a3b`; accepted incremental evidence is `96e2838430347968752e3be6f00be04ea846d165`. The independent zero-partial review is recorded as source/log/hash reconciliation, not fresh execution. No Lean, leanchecker, Lake, cache retrieval, or CI invocation was performed for this preparation. The prepared code awaits independent review and is not a clean validation result.

## Prepared changes

- `scripts/LightEFTExactCI.py` now uses the new exact-gate supervisor for startup and every compiler/checker entry point: version, official cache bootstrap, official cache retrieval, project compilation, official target resolution, singleton replay, and audit. It sets `LEAN_SYSROOT`, `LEAN_PATH`, and `LEAN_SRC_PATH` explicitly. Importing the Python harness is inert. Python optimization is refused because assertions implement gate checks.
- `scripts/LightEFTExactSupervisor.py` uses the existing universal lock `/tmp/distance-sparsification-single-compiler.lock`, without replacing its inode. Under that lock, it requires at least 4 GiB of both system MemAvailable and finite cgroup headroom, more than 2 GiB free disk, and no active Lean/Lake/checker. Contention refuses immediately. UUID receipts preserve failures before spawn, process/disk/memory snapshots, submitted source and harness hashes and snapshots, command/environment, PID/group, UTC/monotonic timing, exit status, and direct-child reaping. The child inherits the lock; cleanup terminates its process group. A lock-contention refusal has no child and no submitted snapshot because admission never acquired the lock; it still has a UUID failure receipt. This is distinct from a compiler invocation.
- `scripts/LightEFTFullAudit.lean` is byte-identical to the accepted `checkpoints/light-eft-linked-rows-pilot-20261017/CompleteAudit.lean` after replacing only its four diagnostic output paths with clean-run `ci-evidence` paths. Actual-owner roots are unfiltered. The audit traverses types, definitions, theorems, opaque bodies, inductive/constructor links, and recursor rules. Inventory and recursive TSV include unsafe and partial columns. All safety findings export before rejection. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Structural missing-module/declaration failures remain fatal as in the accepted audit. No rejection criterion is weakened. Its historical `DIAGNOSTIC ONLY` info label is deliberately preserved; success is determined by exit status and the empty violations file.
- `scripts/LightEFTResolveCheckerTarget.lean` is an unchanged copy of the accepted official-resolution helper. Each checker has a preceding guarded official resolver invocation. The checker supervisor independently re-resolves under lock, requires one module and one unshadowed object, and compares the official resolution file. Aggregate-prefix replay is forbidden.
- The existing general/historical `scripts/LightEFTSequential.py` is unchanged. Production Lean, pins, all historical checkpoints, and the unrelated `lean.yml` workflow are unchanged.

## Clean execution plan (not executed)

Use two separate fresh checkouts: production at the exact frozen source, and verification code at the subsequently reviewed immutable harness commit. The production checkout must have no `.lake`, `.cache-bootstrap`, `.olean`, or `.ilean` inherited objects. This gate never copies objects from existing project workspaces. A separate checkout prevents the old harness embedded in the frozen production commit from being mistaken for the reviewed new harness.

1. Obtain the official Lean 4.34.0 Linux archive from the existing official release URL and verify SHA256 `caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b` before extraction. The prepared dispatch workflow retains this hash check. No runtime shim or network/security setting change is permitted.
2. Verify exact source/harness commits and tracked cleanliness, manifest SHA256 `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f`, and `leanprover/lean4:v4.34.0`. Startup admission must pass before any Lean invocation. Official `lean --version` is itself admitted and must report commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
3. Fetch the nine exact manifest revisions into the clean checkout. Mathlib stays at `5ed2965256430c3649e86755f9576b54eca72435`; no pin updates. Sequentially bootstrap unmodified official Cache.Main and retrieve the official dependency cache. Each bootstrap Lean and `lean --run Cache/Main.lean get` is separately admitted. No default Lake build or parallel Lake scheduler is used.
4. Derive the aggregate import closure and compare all 486 ordered module names, paths, and source hashes to `source-plan.json`. Compile all 486 modules from source into a fresh output tree with `-j1 -DautoImplicit=false -DwarningAsError=true`, explicit `--root` and `-o`. This comprises 429 LightEFT leaves, 56 necessary LightSpanners support modules, and the import-only aggregate. Hash every resulting object.
5. Resolve and replay all 485 leaf/support modules individually. For each, run the accepted official resolver under admission, then `leanchecker -v <exact-module>` under a new admission. Require its sole replay line to name that exact module. Never replay `LightEFTSpanners` or `LightSpanners` as prefixes.
6. Run the exhaustive actual-owner recursive audit under strict options. Export the complete inventory, dependencies, imported modules, and all findings before rejecting safety findings. Preserve row-aligned ordered TSV chunks and reconstruction hash. A pass requires an empty violations file.
7. Recheck production/harness cleanliness and all dependency pins; reconcile UUIDs, lock identity, non-overlap, direct-child reaping, and source snapshots. Preserve raw logs and all failed attempts. Any failed finalization gets a separate diagnostic rather than overwriting the original failure file.

There are 486 project compiles, 485 official resolutions, 485 singleton replays, one audit, one version invocation, and one official cache-get invocation: **1459 compiler/checker invocations plus the bootstrap module count**, all serial. Startup has a receipt but no child. No later execution is authorized by this preparation report.

Future command shape, only after independent review and coordinated authorization:

```sh
cd /absolute/fresh/tested
python3 /absolute/fresh/harness/scripts/LightEFTExactCI.py \
  78cb40c7837db049d645d73696f2e0b724ce8a3b \
  /absolute/official/lean-4.34.0-linux REVIEWED_HARNESS_COMMIT
```

## Read-only CI route assessment

`evidence/ci-route-read-only.json` preserves the GitHub reads and the rejected workflow-collection read. The current `main` workflow directory contains only `lean.yml`, not `light-eft-exact.yml`. The connector rejected the workflow-collection endpoint with `INVALID_ARGUMENT`; no restriction was bypassed. Consequently the existing branch-only workflow must not be assumed dispatchable.

The bounded prepared change to `.github/workflows/light-eft-exact.yml` retains **workflow_dispatch only**, the one sequential job, pinned actions, read-only contents permission, artifact retention on failure, and common repository concurrency group. It adds a separate exact `harness` commit input and checkout, and passes source/harness inputs through quoted environment variables instead of embedding them in shell code. It does not install this workflow on main, dispatch it, or alter unrelated multi-paper workflows. After code review, an explicitly coordinated installation of this single workflow on the default branch is required before the normal dispatch route can be relied upon. Any such installation must separately avoid triggering unrelated jobs. No default-branch write or alternative trigger was attempted here.

The preparation is published only on `light-eft-spanners-checkpoints` with `[skip ci]`; `lean.yml` already excludes that branch and the exact workflow has no push trigger. Remote state was checked before publication.

## Resources and recovery boundary

The saved resource observation has approximately 11.7 GiB free disk and 2.35 GiB cgroup headroom (16 GiB limit), despite substantially more system MemAvailable. There are no live Lean/Lake/checker processes and the common lock is free. This host does **not** currently meet the new memory gate. Preparation needs no recovery action: no data, objects, caches, old logs, or receipts were deleted, evicted, or rewritten. Later execution requires a fresh qualifying runner or an independently reviewed recovery followed by a new admission. Global cache dropping, mass deletion, and bypassing admission are not part of this plan.

## Preparation validation and remaining scope

Seven Python-only tests cover memory boundaries, disk/process refusal, source-bound refusal receipts, lock contention, no-child startup, singleton/shadow/prefix rejection, and inert harness import. Popen is forbidden/mocked where the supervisor is exercised; no Lean/checker is launched. Python syntax and `git diff --check` pass. Static comparison verifies all production graph hashes, audit path-only equivalence, and exact resolver copying. These tests do not establish the behavior of unexecuted Lean verification code or constitute clean proof acceptance.

Theorem 34's general lower theorem remains a substantive open obligation; refutation of the written denominator certificate is not a refutation or repair of the general theorem. Existing represented atom-model execution bounds do not prove physical bit runtime, efficient random generation/seed/packing, or the full printed algorithmic guarantee. This gate changes none of those mathematical or runtime limitations and does not establish whole-paper completion.
