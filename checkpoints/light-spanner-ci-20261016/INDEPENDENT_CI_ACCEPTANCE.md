# Independent clean-CI acceptance: Alternate Light Spanners

Reviewed 2026-10-16. **Accepted for the finite connected main-result scope below.**
This is the independent reviewer's artifact reconciliation, following the separate
mathematical review recorded in [ACCEPTANCE.md](ACCEPTANCE.md). No new Lean compiler,
kernel checker or CI execution was launched by the reviewer.

## Immutable identities

- Tested proof source: `90b270f5442b3ebe50bd41a45f501b2277380d71`.
- CI trigger: `240ae1c3a60b244ab08e6447381c02cec83e963b`.
- Original evidence: `2e5ca7927aaa31dc61c9df3f20657072c780c4cb`.
- [CI run 38846027893](https://github.com/gbodwin/paper-formalizations/actions/runs/38846027893):
  first attempt, one successful verify job `116796641856`.
- [Artifact 12023770784](https://github.com/gbodwin/paper-formalizations/actions/runs/38846027893/artifacts/12023770784):
  2,798,826 ZIP bytes, 696 files.
- Independently recomputed ZIP SHA256:
  `a937fcff075e749aa464ebc60ab3b3fcb8f9523a9a8277982f0a90db49ae9f9b`.

The builder's local proxy download failure remains a valid historical record.
The independent reviewer successfully retrieved the complete ZIP through the
authorized GitHub connector and reconciled the actual bytes. No restriction was
bypassed. The original REPORT.md and ACCEPTANCE.md retain their then-current
"review pending" wording; this additive record supplies the subsequent outcome.

## Checks independently reconciled

1. Every one of the 695 manifest entries matches its file's length and SHA256;
   the manifest covers exactly all artifact files other than itself.
2. The 232-path tracked source inventory matches the immutable Git tree.
   All 65 candidate manifest hashes match the previously reviewed proof source;
   125 relevant source/support files were additionally checked byte-for-byte and
   against their Git blob hashes. The trigger workflow, driver, supervisor and
   recursive audit also match their Git blobs.
3. The inspected workflow checks out the immutable proof source separately.
   The inspected successful gate requires no initial project/dependency outputs,
   fresh checkouts of all nine pinned dependencies, official cache retrieval,
   unchanged dependency tracked sources and unchanged project tracked sources.
   These are successful CI checks, not fresh reviewer dependency compilation.
4. The official Lean 4.34.0 release metadata independently authenticates archive
   SHA256 `caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b`
   ([official release](https://github.com/leanprover/lean4/releases/tag/v4.34.0),
   asset 563514501). The workflow verifies that archive before extraction.
   Version/commit and recorded lean, lake and leanchecker executable hashes match
   the previously authenticated official installation. Official bin PATH setup
   precedes every checker. No shim or toolchain modification is used.
5. All nine dependency pins match the manifest, whose SHA256 is
   `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f`;
   mathlib is `5ed2965256430c3649e86755f9576b54eca72435`.
6. All 161 command receipts reconcile with their UUID records, raw logs and
   submitted-source snapshots. IDs and child PIDs are unique; one exclusive lock
   inode is retained; every child exited successfully and was reaped. Monotonic
   intervals do not overlap. Recorded execution runs from
   03:32:45.267009 to 03:41:45.158212 UTC.
7. The inventory is exactly 60 project builds, 59 singleton kernel replays,
   three audits, 18 sequential cache-bootstrap builds, nine clones, nine pinned
   checkouts, one official cache retrieval and two version queries.
   Project builds use -j1 and autoImplicit=false; all 51 strict builds are
   diagnostic-free. All nine inherited-warning modules match their complete
   diagnostic baselines after only the documented source-root substitution,
   totaling 22 warning headers. Header count alone was not used for acceptance.
8. All 59 replay arguments name exactly one leaf module and every raw replay log
   reports that exact module. All project builds precede these replays. The
   aggregate imports exactly the 59 leaves. The three audits follow the replays.
9. The full recursive audit covers 795 actual-owner roots and 22,323 unique
   constants, including 2,861 private declarations and 14 opaque bodies. All
   roots are safe; the audit traverses types and bodies, including opaque values,
   and rejects unsafe/partial dependencies and disallowed axioms. Independent
   traversal of every exported dependency row gives exactly the exported closure.
   The only axioms are propext, Classical.choice and Quot.sound.
10. All 51 ordered chunks match their own hashes and reconstruct the original
    10,074,280-byte TSV exactly, SHA256
    `55feaf9b104c182b84c8f140e067711520965454f24edad19e4700b66d2a4787`.
    This also matches the previously reviewed local recursive closure.

Authoritative raw logs remain byte-hashed. Only the official-cache convenience
copy uses the supervisor's documented CR/LF-to-LF text conversion; other
convenience logs match raw bytes exactly. The 60 object-hash entries have the
expected exact inventory; object binaries are not included for independent
reviewer rehashing. This qualification does not obstruct acceptance of the
reviewed clean build/replay pipeline. No blocking proof or evidence gap remains
for the stated main-result scope.

## Accepted theorem scope and publication wording

**Main result formally verified for finite connected simple graphs with positive
actual-edge weights, for every real epsilon > 0 and integer k >= 1, with
independently reconciled clean exact-source CI.**

The sorted greedy endpoint has stretch `(1+epsilon)(2k-1)`, an actual contained
input MST and lightness at most `8+(2048/epsilon)n^(1/k)`; the coefficient-form
endpoint gives `(8+2048/epsilon)n^(1/k)`. The actual-edge-weight existence wrapper
removes off-graph nonnegativity requirements by transferring actual-edge walks,
weights and MST optimality from a nonnegative extension. It does not assert
definitional equality of differently extended greedy runs. Singleton lightness
uses totalized zero division. There is no hidden epsilon <= 1 assumption.

- [Greedy theorem and coefficient-form lightness](https://github.com/gbodwin/paper-formalizations/blob/90b270f5442b3ebe50bd41a45f501b2277380d71/An%20Alternate%20Proof%20of%20Near-Optimal%20Light%20Spanners/LightSpanners/MainTheorem.lean#L13)
- [Actual-edge-weight existence endpoint](https://github.com/gbodwin/paper-formalizations/blob/90b270f5442b3ebe50bd41a45f501b2277380d71/An%20Alternate%20Proof%20of%20Near-Optimal%20Light%20Spanners/LightSpanners/WeightExtension.lean#L24)

Preserve the documented global subdivision-budget repair, chord-only strict
bound, t+1 hiker layers with t shuttle moves, and all-epsilon +n baseline repair.
Historical incomplete-status source comments are superseded only at the
assembled-candidate level as explained in ACCEPTANCE.md; frozen source is unchanged.

Excluded: unused warmup/background results, disconnected/MSF assembly, runtime,
and cited lower-bound tightness results. Acceptance does not assert that every
printed statement of the paper has been formalized. This documentation-only
record changes no proof, raw evidence, manifest, toolchain or CI configuration.
