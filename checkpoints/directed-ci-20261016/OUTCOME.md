# Clean directed endpoint CI: independently accepted

The single exact-source gate [run 38831592710](https://github.com/gbodwin/paper-formalizations/actions/runs/38831592710), job `116751375470`, completed successfully on its first attempt at 2026-10-16T00:52:13Z. This is a clean execution record for the bounded directed endpoint; it does not repair missing historical timing evidence or establish whole-paper completion.

## Immutable identities

- Tested mathematical source: `58116f153e48e57a055767cabfd1bc89f622214d`.
- Gate preparation: `4cfd80fe5009519c06cd4350c0167b297063964b`.
- Normal push trigger: `2f9cdb4b4aaf336b99b97bef7a16927c8da3b289`, branch `integration/conditional-plus6-ci-20261015`.
- Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; archive SHA256 `caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b`.
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435`, all nine dependency pins checked; manifest SHA256 `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f`. Official cache retrieval succeeded.
- [Artifact 12017312820](https://github.com/gbodwin/paper-formalizations/actions/runs/38831592710/artifacts/12017312820): 937,681 bytes, 196 files reported by upload; GitHub-reported SHA256 `f35757c6595b065379778bf796a0c77d73b354c15e40676c82457c663e1f44b3`.

## Executed checks

The retained decoded job log records 60 supervised commands, all exit zero: ten project compilations and ten individual kernel replays, plus setup, cache, version and audit commands. Five directed modules compile with `-j1 -DautoImplicit=false -DwarningAsError=true`; the five imported support modules reproduce exact inherited diagnostic baselines (13 warnings: eight ConsistentTiebreaking, two each Hitting and PlusFourParameters, one Amplification). ParameterBounds has zero warnings. The recursive audit is strict and checks 119 actual-owner roots, including 82 selected declarations, 18,093 recursive constants and 14 opaque bodies; only `propext`, `Classical.choice`, and `Quot.sound` are allowed axioms.

Every gate compiler/checker invocation uses the common exclusive-lock supervisor, with UUID allocation under lock, raw output, child and supervisor PIDs, lock identity, UTC and monotonic timestamps, and child-reaping receipts. The gate's final assertions require unique attempts, one lock inode, nonoverlapping intervals, successful exits and reaped children. Those assertions passed in CI. Exact command/options, source/object hashes, individual replay output, audit inventories and lock receipts are in the artifact. The independent reviewer has now extracted and reconciled them; see the acceptance addendum below.

The workflow additionally emitted a GitHub platform warning about pinned actions targeting deprecated Node.js 20 being run under Node.js 24. This is separate from the 13 inherited Lean warnings. The unrelated general workflow `38831592636` was skipped; no multi-paper build ran.

## Preserved evidence and limitation

`monitoring/` retains the decoded full job log, terminal run/job metadata, artifact metadata, log-level reconciliation, pretrigger and terminal CI-idle observations, local idle observation, and the failed artifact-byte download diagnostic. The authorized connector supplied artifact metadata and a download reference, but reading its bytes from this execution environment returned HTTP 403. The SHA256 above is GitHub-reported, not a locally computed ZIP digest. No credential or security-setting changes or restriction bypasses were attempted.

`reconcile_artifact.py` is a prepared read-only checker for a reviewer who can retrieve and extract the artifact. It has not been run here. The independent reviewer subsequently verified the archive digest and manifest, source/object hashes, all command/attempt receipts, replay logs, warning baselines, and recursive audit. The successful CI status and gate assertions are not substituted for that independent artifact reconciliation.

Local compiler/checker activity stayed off throughout preparation and CI; supervisor lifecycle tests used Python stand-ins only. Terminal checks found the common lock free, no local Lean/Lake/checker process, and zero repository runs in progress, queued, waiting, pending or requested. Raw failed attempts and the explicitly labeled historical reconstruction remain preserved. Prior acceptance is recorded as source/log/hash reconciliation, not fresh local execution.

## Mathematical boundary

This endpoint covers finite loopless directed input arcs with finite nonnegative real weights, including zero weights and unreachable pairs. It establishes mathematical existence within that domain. Signed weights, parallel-edge representation, self-loop normalization and algorithmic runtime are outside this acceptance. Reachability partials and the Theorem 5.2 citation mismatch are unchanged; no stronger printed theorem is declared false. Accepted conditional and subset +2 sources, certified branch, and websites are unchanged. No further proof development or CI rerun is initiated pending review.

Independent review subsequently downloaded the 937681-byte artifact and verified its reported SHA256, all 195 manifest entries, all 60 UUID receipts (lock/PIDs/non-overlap/reaping), and byte-identical 119-root audit. The fresh sequencing gap is closed. This is reviewer-reported source/log/hash reconciliation, not a proof rerun. Historical timing qualification remains. The executed gate counted 14 raw occurrences of `warning:`; one is a hint, so the actual diagnostic count is 13. Raw CI output and artifact metadata are preserved unchanged.
