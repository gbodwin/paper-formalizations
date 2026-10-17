# Light EFT exact gate: review fixes, preparation only

The independent reviewer rejected harness `a02bb55db31aa7548a683c3fe6a3827795816b0b` for execution and accepted preservation/hash evidence `09b71938c4edd2617fe9694eee379aba6da0f513`. This additive checkpoint addresses the three code findings and records remaining execution blockers. All prior checkpoints remain byte-for-byte unchanged. No Lean, leanchecker, Lake, dependency-cache CLI, or CI was run. Harmless Python lifecycle tests were explicitly permitted and are distinguished from compiler receipts below.

Frozen production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`, with accepted incremental evidence `96e2838430347968752e3be6f00be04ea846d165`. These changes are unreviewed preparation, not execution authorization, clean validation, or proof acceptance.

## 1. Remove hidden Lean cache entry points

The pinned mathlib `Cache/IO.lean` initializer at lines 124–129 launches `lean --print-prefix`. The saved excerpt and whole-file hash are in `evidence/pinned-cache-initializer.txt` and `pinned-cache-source.json`. Explicit LEAN_SYSROOT does not avoid that initializer. The old outer admission did not admit or receipt this child and did not justify overlapping Lean processes.

The new harness removes the entire Cache.Main bootstrap and get path. There is no fallback to Lake, a cache Lean executable, or a modified runtime. `LightEFTDependencyArtifact.py` downloads and validates a separately reviewed dependency-only tar artifact using Python, without any subprocess. The committed `LightEFTDependencyArtifact.json` deliberately has status `UNAVAILABLE_REVIEW_REQUIRED`: no permissible reviewed artifact is currently available or claimed. The harness refuses that status **before its first Lean invocation**, including version reporting.

The design requires an immutable reviewed specification binding:

- exact URL, byte length and SHA256 of the artifact, and SHA256 of its inventory manifest;
- all nine package revisions, the unchanged lake-manifest hash, and official Lean 4.34.0;
- a provenance-review link to immutable GitHub evidence;
- every object's path, bytes, SHA256 and source-file SHA256 in the exact pinned dependency checkout;
- exact official `cache.mathlib.org` archive URLs and archive SHA256 values, with each object linked to its originating archive.

Before enabling the spec, independent provenance review must establish how those official archive identities map to the pinned source/module graph, the hash of the unmodified official extraction tool, the extraction commands and file mapping, and the final bundle hash. A non-Lean assembler can package already independently authenticated official cache archives, using the official archive extractor without loading Cache.Main. No such assembler run, authoritative module-to-archive inventory, or resulting artifact is being represented as available here. A string claiming an official URL is not provenance proof: the artifact and complete provenance must be independently reconciled before the reviewed spec can change. Existing local dependency objects are not silently repackaged as a trusted artifact.

The consumer allows only unique regular files under `.lake/packages/<one of nine pins>/.lake/build/lib/lean/`, with `.olean`, `.olean.private`, `.olean.server`, `.ilean`, or `.ir` suffixes. Every corresponding `.lean` source must hash to the manifest in the pinned dependency source checkout. It rejects traversal, links, duplicate paths, unexpected files, existing outputs and LightEFT/LightSpanners project objects. It validates the entire inventory before installation and hashes installed objects again. Missing native libraries or other unsupported artifact types must be addressed by further reviewed design, never an implicit build/cache fallback. Downloads, failures and the full manifest are retained. Artifact hashes are streamed rather than loading a potentially large bundle into memory.

**Remaining exact blocker:** no reviewed artifact URL/hash/size, authenticated official-archive inventory, and provenance reconciliation have been supplied. The committed gate therefore intentionally cannot start. This is a prepared consumer contract, not successful dependency acquisition.

## 2. Effective cgroup discovery and process lifecycle

`LightEFTCgroup.py` reads process membership, mountinfo and namespace identity instead of assuming `/sys/fs/cgroup` is the process's resource domain. It maps the unified membership through a full cgroup-v2 mount, decodes mount escapes, walks every applicable non-root ancestor, and takes the minimum finite `memory.max - memory.current`. It retains each ancestor observation, raw membership/mountinfo, namespace inode and system MemAvailable. Missing or malformed accounting, ambiguous mappings, truncated hierarchy views, and membership/mount changes refuse admission. A literal `max` is the only unlimited value for a controlled domain; missing accounting is never converted to unlimited.

The supported execution domain is deliberately conservative: the **initial Linux cgroup namespace**, identified by the kernel's `CGROUP_NS_INIT_INO = 0xEFFFFFFB`, and a visible full hierarchy. Non-initial namespaces are refused, including an apparently normal `/` root: hidden ancestor budgets cannot be established from that view alone. The verified initial hierarchy root is excluded by the kernel's resource-controller semantics, not by treating missing memory files as infinity; its memory-controller metadata and domain type are required. Restricted/containerized runners need a separately reviewed host-visible accounting design, not a bypass flag. The current environment has a non-initial namespace and is refused by this design regardless of apparent mount-root headroom. The earlier below-4-GiB observation remains historical and is not promoted to an effective current budget.

The 4 GiB system and effective cgroup requirements, more-than-2-GiB disk check, no-other-compiler check, universal lock, source/harness snapshots, and unique receipts remain. Every actual Lean/checker entry is still separately admitted. The official sysroot and search paths stay explicit.

`LightEFTProcessLifecycle.py` enables Linux subreaping before child spawn and restores the prior setting after cleanup. The supervisor refuses preexisting children. Cleanup terminates and reaps adopted descendants, including a descendant that changed its process group, before releasing the lock. It records observed descendants and adopted wait statuses and requires `all_descendants_gone` during reconciliation. It will retain the lock and continue cleanup if a descendant cannot be reaped rather than release it and start another compiler. Production executable validation still permits only the explicit official Lean/checker paths; there is no test-mode environment switch or runtime shim.

References for independent code review: [kernel cgroup-v2 documentation](https://docs.kernel.org/admin-guide/cgroup-v2.html), [Linux namespace constants](https://github.com/torvalds/linux/blob/master/include/uapi/linux/nsfs.h), [mountinfo fields](https://man7.org/linux/man-pages/man5/proc_pid_mountinfo.5.html), and [subreaper semantics](https://man7.org/linux/man-pages/man2/PR_SET_CHILD_SUBREAPER.2const.html). These are design references, not evidence of executing the proposed Lean gate.

## 3. Success only after reconciliation

The gate records `CHECKS_COMPLETE_PENDING_RECONCILIATION` after its mathematical checks. Finalization verifies receipts, source snapshots, non-overlap, reaping, exports and evidence hashes. `EXACT_SOURCE_PASS` is printed only after the complete try/finally has returned successfully. A finalization exception writes FAILED diagnostics and prevents that marker. A Python-only control-flow test covers the failure case. Evidence hashing now streams large files.

## Preserved clean plan

The unchanged source-plan binds all 486 source modules and their order/hashes. The unexecuted sequence remains 486 fresh strict project builds, 485 guarded official target resolutions, 485 individual leaf/support replays, and the exhaustive audit. Including one separately admitted official version invocation, this is **1458 Lean/checker invocations**, with no cache/bootstrap Lean invocations. Startup has no child. No inherited project objects, default Lake build, aggregate-prefix replay, worker parallelism or pin changes are permitted.

`LightEFTFullAudit.lean` is unchanged from the preceding prepared commit and still equals the accepted exhaustive audit after output-path substitution only. Its unsafe/partial columns, unfiltered actual-owner inventory, type/body/opaque traversal, allowed axiom set, and export-all-safety-findings-before-reject behavior are preserved. The accepted official singleton resolver is likewise unchanged. Verification code, production source, package pins, and the future dependency artifact are bound separately in receipts and manifests.

## CI installation proposal — not installed or dispatched

Fresh read-only main inspection is preserved in `evidence/main-route.json`. Main's `lean.yml` has **no shared concurrency block**. The preceding report's checkpoint-branch concurrency observation was insufficient to establish repository-wide exclusion.

The proposed installation is exactly two workflow changes on top of the freshly checked default-branch commit, never a merge of this checkpoint branch:

1. Apply `main-shared-concurrency.patch` to the observed main `lean.yml`, adding only workflow-level group `paper-formalizations-single-compiler` with `cancel-in-progress: false`.
2. Install the single `light-eft-exact.install-template.yml`, replacing `REVIEWED_HARNESS_COMMIT` with the full independently approved harness SHA. Its job guard fixes both the frozen production SHA and reviewed harness SHA; checkouts use those exact inputs. It remains dispatch-only, read-only contents permissions, one sequential job, pinned actions, explicit official archive SHA, and failure artifact preservation. The template guard cannot match until deliberately filled in.

Both workflows then serialize through the same repository concurrency group. Before installation/dispatch, all existing ungrouped runs must drain and active workflow definitions/refs must be reconciled: an older branch or manually selected workflow ref lacking the group can still run outside it. The main-only patch does **not** prove exclusion for arbitrary stale branch workflows. A coordinated no-unguarded-trigger window or further narrowly reviewed exclusion for every relevant active ref is still necessary. No queue read alone closes that future-race gap. Installation must use CI-skipped publication and must not merge unrelated checkpoint contents. No main change, security-setting change, cancellation, or dispatch has been attempted.

**CI remains blocked** pending the dependency artifact, independent code review, a qualifying runner/accounting view, and verified exclusion of ungrouped CI. The default-branch installation proposal is not a claim that safe dispatch is currently available.

## Preparation tests and evidence

The latest new suite passes 20 tests: cgroup root/nested/ancestor limits, overcommitted ancestors, missing/malformed files, escaped mountpoints, subtree binds, ambiguous mounts and namespace refusal; artifact filtering/hash installation without a subprocess; successful/nonzero harmless children; SIGINT/SIGTERM/SIGHUP; inherited lock exclusion; and an orphan that changes session and ignores SIGTERM, requiring SIGKILL and adoption/reaping. The seven earlier Python-only admission tests also pass. All raw test-run logs are retained. The latest lifecycle runs and the preceding receipt-preserving run retain UUID receipts, raw output and submitted Python snapshots in `evidence/harmless-python-receipts`.

These lifecycle tests use actual harmless Python processes, a temporary fixture lock, and mocked ample memory/executable validation within the test process only. They are **not** compiler receipts, live production admission, or a claim of 4 GiB available on this host. The initial test run's summary log is retained; its temporary receipt directories were not exported. Later runs explicitly export them. No failed test logs were discarded. No Lean/checker run occurred.

The source/module hashes, accepted audit/resolver, historical checkpoint trees, and all pins are statically reconciled. No production proof or website changed. The general Theorem 34 lower claim remains a substantive open obligation; modeled runtime results do not become physical bit-runtime or full algorithmic guarantees. No whole-paper completion is claimed. Stop for independent code review after additive CI-skipped publication.
