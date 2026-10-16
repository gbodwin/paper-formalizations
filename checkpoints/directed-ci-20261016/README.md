# Directed endpoint procedural closure and exact-source CI

The parent reports independent review accepts the bounded directed-distance mathematics and source/log/hash evidence at source `58116f153e48e57a055767cabfd1bc89f622214d` and evidence `1e4d394b1d2dbf389907ac442c2440cbac096f1a`, with a procedural qualification: the historical non-overlap of final local calls cannot be established from missing timestamps/PIDs/lock receipts. The overwritten failed JSON reconstruction remains labeled. **The entire historical validation is not described as sequential.** The reviewer is idle. This record is not fresh execution.

The new gate freezes exactly **58116f153e48e57a055767cabfd1bc89f622214d**; no mathematical source edits are part of this closure. It uses the existing single-job push mechanism and official Lean 4.34.0 archive digest, all nine manifest revisions, and normal official mathlib cache retrieval. It compiles the actual import closure of `SlackSparsification.DirectedPreserver`: five directed modules and five imported support modules, then individually replays all ten leaves. The five directed compilations and audit are strict. The support sources must reproduce their exact inherited diagnostics: eight warnings in ConsistentTiebreaking, two each in Hitting, PlusFourParameters and Amplification, zero in ParameterBounds (14 total). The audit requires 119 roots, 18,093 recursive constants, 14 opaque bodies and the three allowed axioms.

## One common runner

`scripts/SequentialLean.py` is the common entry point for every compiler/checker call in the new gate, including version calls, cache bootstrap, and cache execution. Historical runner scripts are preserved as evidence and are not used. All new local compiler/checker invocations must likewise use this runner. No local Lean execution is performed while preparing or running this gate.

The runner uses the stable `/tmp/distance-sparsification-single-compiler.lock` inode and allocates unique UUID attempt directories only after acquiring the exclusive lock. Each durable receipt records UTC and monotonic start/end times, supervisor and child PIDs, process group, lock FD/device/inode, command, relevant Lean search paths, exit status, and whether the child was reaped. Raw stdout/stderr is retained separately per unique attempt. Normal completion writes receipts before releasing the lock.

The official ELF compiler/checker is executed directly and inherits the locked open-file description with `pass_fds`; no Lake compiler-launching intermediary is used. Compiler search paths are explicitly assembled from the pinned package checkout/build directories and official sysroot. This is external process supervision, not a Lean runtime patch or shim. The cache program itself only launches its standard noncompiler helpers.

Catchable SIGTERM/SIGINT/SIGHUP interruptions terminate the child process group, escalate after five seconds if needed, and wait for child reaping while retaining the lock. A hard-killed supervisor cannot run cleanup, but the surviving direct child retains the inherited lock until it exits; no explicit unlock is issued. Incomplete start receipts remain visible. The preparation tests use Python stand-ins only and check mutual exclusion, unique IDs, SIGTERM cleanup, and continued lock ownership after supervisor SIGKILL. Their raw logs/receipts and incomplete hard-kill receipt are preserved under `supervisor-tests/`. No test uses Lean or another worker.

The CI gate checks successful intervals for non-overlap, unique attempt IDs, one lock inode, and reaped children before recording PASS. CI has one job, no matrix, a repository-wide active-run preflight and the shared single-worker concurrency group. The source checkout is fresh and tracked source hashes are rechecked before and after. Audit outputs are retained in the artifact. There is no default multi-paper build or further proof development.

## Scope and provenance

Finite nonnegative real weights, loopless directed input arcs, and mathematical existence only. No signed-weight, parallel-edge, self-loop-normalization or algorithmic-runtime claim. Theorem 5.2's distance/reachability citation mismatch remains a citation mismatch; no proof that the stronger printed theorem is false is claimed. Prior proofs, evidence, failed/reconstructed attempt records, certified branch, and websites are preserved. No whole-paper completion claim.

The terminal run identities and artifact status will be added to OUTCOME.md. Independent review of that clean execution is the next step before resuming reachability.
