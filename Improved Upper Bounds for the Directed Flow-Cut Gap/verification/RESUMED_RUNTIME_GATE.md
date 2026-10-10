# Resumed exact193 runtime gate

This branch preserves all 193 proof components and their import-only root from
6b8a1e24b087378384898f44108c21345a2a089b byte-for-byte. It adds the recovered
eight-body runtime gate absent from that earlier successful CI run.

The original smoke source is SHA-256
5f4b7ab9795c66743f698323bd2c27f72439a2ede27308fb78c14bc646b3b97f.
The single-main driver is a fresh body-preserving transformation, not a
recovered old driver or verification receipt. Replacing its eight named IO Unit
headers with the original #eval headers reproduces the original source exactly;
only the main function and ordered START/DONE markers are appended.

CI first checks the exact proof-source and runtime-driver hashes, then runs its
normal build, strict repaired-module compilation, exhaustive owned-declaration
axiom audit, existing execution regressions, this eight-body runtime gate with
explicit printed-charge checks, and project-component kernel replay.

This commit does not assert a CI result before that run finishes. The verified
174-component partial baseline remains fc11ede6. The larger 251-component
working integration and 105 preserved drafts are separate, unverified work.
Full-paper completion, weighted provider construction, full algorithm/runtime
joins, and the companion reading site remain open.
