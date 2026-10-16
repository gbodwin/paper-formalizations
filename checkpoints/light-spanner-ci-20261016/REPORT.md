# Clean light-spanner exact-source CI

Status: clean exact-source CI succeeded on its first attempt; independent artifact
review remains pending. The finite connected main-result mathematical review was
accepted separately, as recorded in ACCEPTANCE.md. Publication is not claimed.

- Source: `90b270f5442b3ebe50bd41a45f501b2277380d71`.
- Trigger: `240ae1c3a60b244ab08e6447381c02cec83e963b`.
- [Run 38846027893](https://github.com/gbodwin/paper-formalizations/actions/runs/38846027893), job `116796641856`: success.
- [Artifact 12023770784](https://github.com/gbodwin/paper-formalizations/actions/runs/38846027893/artifacts/12023770784): 2,798,826 bytes; 696 uploaded files.
- GitHub/upload-reported ZIP SHA256: `a937fcff075e749aa464ebc60ab3b3fcb8f9523a9a8277982f0a90db49ae9f9b`.

The terminal job log reports 161 sequential commands, 60 builds, 59 individual
kernel replays and three audits. All 51 strict builds passed; all nine inherited
warning modules matched their complete normalized diagnostic baselines, totaling
22 warning headers. The recursive audit passed for all 795 actual-owner project
roots, 22,323 recursively visited constants and 14 opaque bodies, with only
propext, Classical.choice and Quot.sound. All 51 ordered audit chunks and the
original full TSV are in the artifact. Unique source-bound UUID receipts, one
lock inode, non-overlap and reaped children passed the gate's reconciliation.
Source preservation and clean pinned dependency acquisition checks passed.

No CI invocation failed. The prior local PATH launcher failure remains preserved
in the accepted recovery evidence; official PATH setup prevented that failure in
this fresh run. GitHub Actions Node deprecation notices are infrastructure messages,
not part of the 22 Lean warning headers.

The decoded terminal log and API run/job/artifact metadata are preserved under
`evidence/`. `result-from-job-log.json` extracts the result from that log; it is not
a claim of independent local proof execution. The reported archive digest was
reconciled between artifact metadata and the upload log.

Artifact access qualification: the connector successfully returned file reference
`file_00000000ed9881fdb13556bea17ec0b0`, but this environment's attempt to read the
ZIP bytes failed with `URLError: <urlopen error Tunnel connection failed: 403 Forbidden>`.
The raw traceback and diagnostic are preserved. No bypass, extra credentials or
security/network changes were attempted. Consequently the ZIP digest was not
independently recomputed here. `reconcile_artifact.py EXTRACTED_DIRECTORY` is a
syntax-checked read-only handoff helper for complete manifest/source/receipt,
full diagnostic-body, replay and recursive-closure reconciliation; it could not
be exercised against the unavailable ZIP bytes.

Terminal checks show no active repository CI, no local compiler/checker and a
free common lock. No local Lean invocation occurred during preparation or CI.
The unrelated multi-paper workflow was skipped. Paused for independent artifact
review; no website publication or whole-paper acceptance is claimed.
Tested source is pinned to `90b270f5442b3ebe50bd41a45f501b2277380d71`.
The preceding independent review is recorded separately in ACCEPTANCE.md.

One sequential job on `integration/light-spanner-ci-20261016` performs fresh
checkouts of all nine pinned dependencies, official cache retrieval, 60 builds,
59 singleton kernel replays, and three audits. Project outputs begin empty.
No default multi-paper Lake build is invoked. The general repository Lean job is
explicitly skipped on this integration branch. A repository-wide idle preflight
runs before the job acquires/uses the shared compiler lock.

Official Lean 4.34.0 archive SHA256:
`caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b`.
Lean commit: `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
Manifest SHA256: `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f`.
Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
The official bin directory is on PATH before any checker and explicitly recorded.

Builds use `-j1 -DautoImplicit=false`; 51 warning-free modules, including the
aggregate, additionally use `-DwarningAsError=true`. Nine inherited-warning
modules must match their complete prior diagnostic text after replacing only the
original source-worktree root with the CI source root. Exactly 22 warning headers
are expected; header count alone is not an acceptance condition. Raw diagnostics
and baseline hashes are retained.

Every compiler/checker invocation has a source snapshot/hash and UUID receipt,
common exclusive lock inode, child PID, start/end UTC and monotonic times, exit
status and reaping. All operations are sequential. Original all-declaration and
selected-axiom audits are followed by the recursive actual-owner audit over all
795 project roots; every leaf must be represented. The complete artifact retains
raw logs, source/object/toolchain hashes, receipts, full recursive closure, ordered
chunks and reconstruction/hash manifests, including any failures.

Local compilers remain stopped during CI. No website or frozen source is changed.
Publication and whole-paper completion are not claimed.
