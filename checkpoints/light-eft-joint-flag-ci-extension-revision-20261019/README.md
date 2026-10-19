# Revised ordinary-event staged CI gate — local review only

This revision addresses the independent rejection of the exposed preflight-gated candidate. Nothing is committed, staged, pushed or executed in CI. HEAD remains `c66b8f879008262139f6d09f7130b3a6e055a866`. No Lean/checker, lock acquisition, retrieval, website or SCC work occurred. The proof remains uncompiled and unaccepted.

## Ordinary workflow stays usable

The workflow begins from the original checked-in `.github/workflows/lean.yml`, retaining every existing event, branch condition, action, check, target, timeout, permission and concurrency group. The revision adds only job-wide `LEAN_NUM_THREADS: '1'`, the staged verification step after existing checks, and always-run evidence upload. It adds no dispatch input, mandatory preflight, handoff JSON, readiness flag, scope approval predicate or artificial failing prerequisite. Automatic push and pull-request runs reach the staged phase normally when their existing checks succeed. Ordinary manual runs are also supported. The existing ignored checkpoint branch is not used as a substitute for normal publication.

The runtime binds directly to the exact event `GITHUB_SHA` (which must equal checked-out HEAD), run ID and positive run attempt. The workflow SHA is recorded separately, so normal event contexts are not rejected by an unnecessary workflow-SHA equality condition. Each run/attempt receives fresh output, evidence and lock paths. A later GitHub rerun is a distinct run attempt; the four-operation staged phase itself has no retry.

The CI specification is authenticated against the event checkout before use, then binds exact source files, harness and workflow bytes. It pins the preserved 12,533-byte theorem source SHA256 `7187c40f88f68caa69ef7fb188acc29eba9bed4b5b065c62a994f2fc3118d901`, complete owner-audit source SHA256 `b209015ffd54b89c1ad9a1b99a5e0b8832743c10ca0f060d4e578b453a148fd3`, resolver, official binaries, nine dependency pins, 77 source dependencies, 78 imports, 16 required public roots and eight interfaces. No staged proof or accepted source/object pair was modified.

## Bounded serialization finding applied

The independent reviewer supplied a bounded pinned-source finding: current trusted ordinary Lake module/object/executable paths use default-priority task work and blocking proc; `IO.Process.output` waits for compiler exit before `Task.get`, and the dedicated task only drains stdout. No overlapping compiler-spawn path was found there. The job-wide supported worker setting therefore covers the initial build, cache-tool bootstrap, `mk_all` and later checks. Every explicit staged child environment also preserves `LEAN_NUM_THREADS=1`.

This records independent source inspection, not fresh execution here. It is not a universal process semaphore for arbitrary future custom tasks, and not a distributed lock. Changed task priorities, nonblocking/custom compiler-spawn paths or environment overrides need renewed review. No unsupported Lake job flag is introduced. The staged phase independently uses the preserved sequential child supervisor and complete terminal/reaping checks.

The five existing paper checks are retained verification covered by Greg's approval. They are not an artificial scope blocker and do not authorize new research/extensions on those papers. All original default targets, VFT audit, module-index generation, all-library audit and kernel replay steps remain unchanged.

## Operator-exclusive window before publication

Cross-host coordination is external to the CI program. Before normal publication, the operator establishes one exclusive CI window: independently refresh repository-wide live CI status, finish/park independent review, stop local compiler activity, then park this ordinary executor. The executor remains parked until ALL resulting runs/attempts are terminal, including queued/waiting/pending/requested runs and cancellations. Do not resume after only one workflow or artifact completes.

There is no dispatch-only document requirement. CI records its own event identity and fresh PID/boot/namespace facts after planning; it does not self-assert the separate executor is paused. The existing shared GitHub concurrency group serializes repository workflow runs. The operator window supplies coordination with this separate executor and stays in force until explicitly released.

Independent GitHub connector reads at 01:49 UTC on 2026-10-19 reported zero in-progress, queued, waiting, requested and pending runs. That resolves the historical tunnel-read gap for that observation, not future idleness. Refresh immediately before future publication/execution. No denied tunnel request was retried here.

## Real staged controls retained

Compile, exact singleton resolution, singleton replay and full owner audit run in order, stopping at the first failure. The preserved reviewed lifecycle engine, kernel limit handshake, owned terminal observation, waitid/wait4 matching, descendant cleanup, package/shadow checks, output guards and complete receipt reconciliation remain. Admission is 3/3/4/4 GiB; applicable CPU/address-space/wall/RSS/anonymous-growth/PID/output controls and strict warnings are unchanged. New Python control code uses a fresh absent cache prefix and `-B`.

The fresh CI accounting, inventory and lease adapters are retained from the historical candidate, with the lease callback now checking current CI identity rather than an external reservation. Accounting refuses hidden/truncated/overmounted/incomplete/drifting views, retains raw/partial diagnostics and makes no old local-identity claim. Actual hosted-runner compatibility remains unexecuted. The lock is newly and exclusively created within the fresh CI run directory; no local device/inode or epoch is transplanted. Release requires kernel no-children verification.

The full recursive audit still discovers every actual-owner declaration, including generated/private roots and the private identity theorem; traverses types/bodies and inductive/constructor/recursor links; and rejects disallowed axioms, unsafe/partial declarations, owner/import discrepancies and missing required roots/interfaces. No synthetic count is substituted for actual Lean output. Dependency/cache bytes and signatures retain their explicitly qualified fresh-CI provenance; no historical preservation or authenticated dependency provenance is inferred from a clean runner or URL.

## Tests, history and review package

The latest run passed **24 synthetic/static tests, zero failures/errors**. The earlier 23-test passing run is preserved. Tests forbid actual process launch, flock, proc/sys and resource probes. They cover ordinary events and positive attempts without handoff/readiness data, exact event/spec/source binding, job-wide and explicit child worker settings, retained workflow controls, first-failure stop, all roots/interfaces/private/generated owner coverage, accounting/stop boundaries, immutable input/link/shadow boundaries and full receipt-verifier equivalence. Fixture objects and fabricated audit summaries are not Lean results.

An initial local source-transformation assertion matched a documentation word and stopped before writing the transformed gate. Its diagnostic and partial files were preserved; the corrected transformation uses AST/function checks. No compiler failed or ran in this revision.

The rejected candidate's directory and 750-entry manifest remain byte-identical. Before editing the one exposed mutable workflow path, its exact bytes were saved as `historical-exposed-workflow.yml.txt`; `historical-preservation.json` records that mapping. The old manifest is historical and is not expanded or rewritten to describe this revision.

Review `workflow.diff`, `revision-vs-rejected.diff`, `complete-proposed-source-and-CI.diff`, test logs, static preservation results and `OPERATOR-WINDOW-AND-SEQUENCE.md`. Publication and compiler execution still await independent review. No whole-paper or joint-law acceptance is claimed.
