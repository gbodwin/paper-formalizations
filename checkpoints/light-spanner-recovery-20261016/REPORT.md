# Recovery of the immutable light-spanner main-result candidate

Status: fresh sequential local validation passed; independent review pending.
This checkpoint does not claim publication or whole-paper completion.

Candidate source: `90b270f5442b3ebe50bd41a45f501b2277380d71`, recovered from
`light-spanner-main-result-draft` into the separate worktree
`/workspace/light-spanner-verification`, branch
`checkpoint/light-spanner-recovery-20261016`.
Initial verification harness: `008f05101bb16502b67a9b29bd0ab8559d2f077d`.
Replay-resume harness: `43b999d0de74aa39b60c0c008d75ec57875c09e9`.
No candidate proof, aggregate, original audit, pin, or retained historical evidence
was modified. The accepted distance-sparsification work remains separate and
unchanged; its acceptance is recorded from the user's report, not freshly executed.
No deleted/external ChatGPT workspaces or duplicate workers were used.

## Recovered source and historical evidence

All 65 entries in `verification/main-result-source-hashes.json` match byte-for-byte:
59 LightSpanners leaves, aggregate, two original audits, lakefile, manifest and
toolchain pin. The aggregate imports exactly all 59 leaves. All 17 final component
review hashes match. All 59 distinct historical kernel-pass names reconcile with
the current module inventory. `historical-reconciliation.json` records retained
verification-file hashes and bounded review references.

The main-result verification note, retained build/axiom/kernel logs, component
index, semantic reviews, exact statement coverage and source corrections were
read. Older semantic reports sometimes bind pre-elaboration source; the final
component index and final pipeline re-review bind the final affected files.
This is historical source/log/hash reconciliation, not a new independent semantic
review. The historical 42-module CI does not validate this 59-module candidate.

## Exact mathematical scope

`LightSpanners.near_optimal_greedy_spanner` constructs the sorted greedy output
with stretch `(1+epsilon)*(2*k-1)` and an actual input MST contained in that output.
Its explicit bound is `8 + (2048/epsilon)*n^(1/k)`.
`near_optimal_greedy_lightness` gives the stated fixed-epsilon form
`(8+2048/epsilon)*n^(1/k)`.
`exists_near_optimal_spanner` in WeightExtension transfers spanner, MST, weighted
distance and lightness to weights positive only on actual graph edges. It uses
`max(w,0)` internally and does not claim equality of two differently extended
greedy runs.

The domain is finite connected simple graphs, positive actual-edge weights,
every real epsilon>0 and natural k>=1. The greedy-specific theorem additionally
requires globally nonnegative weights; the existence wrapper removes off-graph
restrictions. Singleton inputs use Lean's totalized zero-division convention.
Disconnected MSF assembly, runtime, cited sparsity/lower-bound tightness and unused
warmup/background exposition are outside this package, as detailed by the retained
52-block STATEMENT-COVERAGE inventory.

The recovered proofs preserve all four repairs: the global subdivision vertex
budget, the chord-only strict weight bound, t+1 chord layers with t shuttle moves,
and the +n baseline in the auxiliary all-positive-epsilon weight bound. The usual
no-baseline auxiliary estimate is restricted to epsilon<=1. The finite-uniform
counterexamples do not refute the fixed-epsilon main theorem.

## Fresh execution protocol

The initial driver was `python3 checkpoints/light-spanner-recovery-20261016/verify.py`.
For a fresh reproduction, prepend `/workspace/toolchains/lean-4.34.0-linux/bin` to
PATH before running it in a worktree with empty project outputs. The preserved
resume command is `python3 checkpoints/light-spanner-recovery-20261016/resume.py`.
Project outputs start empty. Only this paper's 59 leaves and aggregate are compiled,
in source-derived dependency order, with official Lean `-j1 -DautoImplicit=false`.
No default Lake build or other paper is run. Each leaf receives its own
`leanchecker -v LightSpanners.MODULE` invocation with exact singleton replay output.
The two original audits and the added full actual-owner recursive audit run strictly
with `-DwarningAsError=true`.

Every invocation uses the copied, hash-preserved common SequentialLean supervisor
and `/tmp/distance-sparsification-single-compiler.lock`. UUID attempt directories
preserve full commands/options, submitted source hashes and bytes, lock inode,
child PIDs, UTC/monotonic times, raw logs, exit status and reaping. No parallel
compiler/checker or CI is started. Compiler warning headers are counted with an
anchored expression and compared with retained historical headers; raw diagnostic
bodies and hints are preserved separately without counting hints twice.

The official Lean 4.34.0 archive SHA256 is
`caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b`,
with executable-reported commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
The manifest SHA256 remains
`615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f`;
all nine dependencies match clean recorded checkouts, including mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Existing pinned dependency cache outputs
are reused; no old LightSpanners objects or other project outputs are on LEAN_PATH.
This is a fresh project-output local verification, not a clean dependency rebuild
or a new CI run.

## Results and preserved failed attempt

All 60 compilations (59 leaves plus aggregate), 59 successful singleton kernel
replays and three audits passed. The original all-declarations audit reports
795 declarations. The stronger recursive audit independently inventories the same
795 actual-owner declarations across every leaf and traverses 22,323 constants,
including 14 opaque bodies. Only `propext`, `Classical.choice` and `Quot.sound`
appear as axioms; unsafe/partial dependencies are rejected. Full recursive TSV,
51 ordered row-aligned chunks and the byte reconstruction manifest are retained.

There are 124 UUID invocation receipts: 123 successful invocations and one failed
initial replay. All have source snapshots/hashes, one common lock inode, disjoint
execution intervals and reaped child processes. The official-version probe also
binds the toolchain-pin bytes. Compilation completed before any replay began.

The initial `leanchecker -v LightSpanners.Basic` failed because the inherited PATH
could not resolve the official `lean` subprocess (`could not execute external
process 'lean'`). This was a launcher-environment failure, not a rejected proof.
Its UUID is `12a6b6d7843c4c0c9c89ec10282e63cf`; raw diagnostics, receipt, original
failure traceback and driver log are preserved. `resume.py` prepends the official
bin directory to PATH, rechecks every source and object hash, and resumes only
replays/audits. No runtime shim, source repair, pin change or recompilation was
needed. The authoritative failed-attempt log is its UUID `raw.log`; the semantic
replay log is the later successful invocation.

Fresh compilation produced exactly 22 warning headers, all matching the retained
main-result build diagnostics. Counts by module: BucketRestriction 3,
PaddingPositions 2, RetainedGraph 3, EndpointSampling 2, EpsilonDomain 1,
SamplingCounting 6, LightnessBound 1, MainTheorem 1, WeightExtension 3. These are
retained linter/deprecation diagnostics; no unmatched warning header or proof
error remains. Hints are not counted as additional warnings. This comparison
matches diagnostic headers, not a claimed byte-identical Lake/direct-Lean log.

`evidence/object-hashes.json` records all 60 newly built objects.
`evidence/commands.jsonl` and `attempts/` retain exact commands/options and raw
execution evidence. `reconcile.py` checks the saved manifests, all source-bound
receipts, exact compile/replay inventory, warning count, recursive closure and
chunk reconstruction without executing Lean. Source and object bytes were checked
before resume, and all 65 candidate manifest entries remain unchanged afterward.
The nine dependency checkouts were rechecked clean at completion.

Terminal state: no Lean/Lake/checker process, common lock free, approximately
23 GiB free disk, 16 GiB memory limit and four-CPU quota. No CI was triggered.
This is fresh local kernel evidence and a review checkpoint, not independent
semantic acceptance, clean CI, disconnected coverage, runtime certification or
whole-paper completion. No new mathematical repair was made during recovery.

Read-only local reconciliation passed for all 567 evidence-manifest entries and
124 receipts. The recursive TSV reconstruction SHA256 is `55feaf9b104c182b84c8f140e067711520965454f24edad19e4700b66d2a4787`
(10074280 bytes, 51 chunks). These are evidence consistency checks, not a
new independent mathematical review.
