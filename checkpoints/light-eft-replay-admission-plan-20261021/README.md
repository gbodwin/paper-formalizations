# Actual-runner admission proposal, source only

Production remains exactly 0747b30af2bafcc57ae2ab89289af59d670c8068. This additive
checkpoint supplies proposed admission code, a proposed paired workflow/script
patch and models for source review. The code has not run on a hosted runner.
No local prior observation qualifies a future runner. No compiler, CI, push or
physical attempt occurs, and the consumed allowance is not renewed. Fast is off.

The unchanged ordinary build stays in place. The new checks justify only the
**new global replay launcher behavior**, rather than introducing a whole-pipeline
admission system. The proposed Python bootstrap step is immediately after the
canonical corollary gate and immediately before global replay. GitHub directly
starts `/usr/bin/python3 -I -B {0}`: there is no new Bash process before its
UID/GID, shell-export and Bash-identity observations. Failure skips replay under
the existing default fail-fast workflow dependency. Existing stages and uploads
are preserved; the existing final evidence upload gains the admission directory.

## Four observations, one Lake setup

1. **bootstrap**, on the actual future runner: obtain exact existing CI/job/source
   identity; require equal real/effective UID and GID; require absent inherited
   SHELLOPTS, BASHOPTS, CDPATH, GLOBIGNORE, BASH_ENV and ENV; admit C.UTF-8/C.utf8
   locale and the existing single-worker setting. Record the actual Bash and
   isolated Python identities, symlink chains, configuration/source bindings,
   inherited five-key environment and selected installed Lake/elan carrier.
2. **before-lake**, in the admitted outer privileged Bash: revalidate the bootstrap
   on the same job/host/source, inherited projection and Lake/elan carrier. Then
   execute that carrier with the exact `env`/Python/inner-shell command. This is
   the single Lake setup, not another setup probe.
3. **enter**, under that actual Lake environment and before inner Bash: revalidate
   the bootstrap and before-Lake record; capture PATH, LEAN_PATH, LEAN_SRC_PATH,
   LEAN_SYSROOT and LD_LIBRARY_PATH exactly, preserving absence versus empty.
   Require the existing pinned Lean/checker hashes, actual LAKE/sysroot agreement
   and PATH-selected checker identity. Record the actual toolchain Lake identity.
   Execute only the fixed privileged Bash argv and hash-pinned complete loop body.
4. **verify**, the first command in the actual inner Bash before any checker:
   revalidate the same host/source/platform and earlier record bindings; compare
   all five environment values, effective checker and tool identities exactly.
   Record actual Bash flags/version. A mismatch, missing record or write failure
   stops the shell under `-e`; no checker is launched. Only then does the unchanged
   567-target loop begin, with a fresh checker process for each target.

The baseline is the real augmented Lake environment that the prior per-module
direct checker launch would receive. Pinned v4.34.0 Lake constructs this environment
before dispatching its child command; changing that child to the read-only Python
observer does not synthesize library paths. The subsequent observation occurs
inside the actual hoisted Bash. No `lake env` environment dump is guessed from
local paths, no extra Lake setup is needed, and no kernel result or import replay
is cached. Source and no-writer assumptions still matter.

Each admission mode has a 90-second alarm, and read-only Git calls have 10-second
timeouts. The alarm is cancelled before either exec handoff so it cannot become
a new replay deadline. Existing supervised child limits and 120/120/5-minute job
envelopes remain unchanged. Admission receipts are owned fresh runner observations,
not compilation receipts, permission tokens, historical continuity or production
manifests. Files are exclusive-create; duplicate/missing/unsafe records fail.
The Lake/elan carrier may legitimately have hard links; their identities/link
counts are recorded and compared. Existing proof-input link policies are untouched.

## Coverage and boundaries

| Condition | Existing coverage | Proposed launcher-specific coverage |
| --- | --- | --- |
| Exact source/caller/job | Existing CI identity, Git bindings and status conjunction | Same identity validator plus live Git bytes and helper/script/workflow rows in all five specs |
| Bash and real/effective UID/GID | Not established by old native child receipts | bootstrap before new outer Bash; repeated identity checks before both handoffs and first checker |
| Shell-option exports | `-p` prevents function import; arbitrary environment equality was not established | explicit inherited absence and normal locale/worker contract on every observation |
| Effective paths and checker | Earlier resolver/audit inputs concern their bounded children, not this ordinary launcher | real one-setup Lake baseline versus actual inner-shell projection, executable and tool comparisons |
| Tool pins | Existing gate tool hashes before their bounded children | same pinned Lean/checker hashes and actual Lake/sysroot identities before new checker launches |
| Cgroup/headroom, native leases, cleanup | Existing CIAccounting/CILease/child_runner at their accepted boundaries | unchanged; this proposal does not claim retrospective admission of the build or replace those guards |
| Repo queues, reservation, no duplicate compiler | Existing coordinated authorization/concurrency plus existing idle/admission checks | fresh external prerequisite remains mandatory; no new unchecked Boolean substitutes for it |
| Immutable config/build/toolchain/environment | Accepted no-writer contract and earlier per-child input checks | configuration/critical-tool/source snapshots repeated; all-file immutability throughout replay remains an explicit prerequisite, not a proved hostile-writer defense |

Pinned-action installation and ordinary dependency provenance qualifications are
retained. Newly recorded Lake/Bash identities do not establish reproducible builds
or authenticated cache provenance. This is not unrelated runner hardening.

## Required source integration before any qualification request

The proposal is not wired into production. All five existing engine lists must
gain the helper, the existing acyclic binding cascade must be refreshed, and the
exact-control verifier must bind the helper/new script and require the adjacent
isolated-Python bootstrap/global-step pair and evidence path. Its reviewed script
hash and finite integration assertions must be updated. Current 0747 specs lack
the helper, so `checked_sources` refuses rather than admitting this candidate.
Review that exact integrated commit sequentially before requesting a separately
authorized bounded run. All old gates, audits, 567 targets, jobs and caps stay.

Models use synthetic observations and owned temporary files with process/exec,
lease/resource and signal actions blocked. They do not execute admission on this
worker or report this worker as qualified. Runtime admission, actual equality,
time savings and budget fit remain unobserved. All 36 mathematical bodies remain
unelaborated and whole-paper acceptance remains open.
