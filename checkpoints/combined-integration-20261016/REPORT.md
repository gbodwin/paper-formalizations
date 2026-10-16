# Combined sparsification integration gate

Status: CI succeeded; independent combined-artifact and scope review is pending.
This is a new combined integration, not reconciliation of the SCC checkpoint.
Whole-paper acceptance is not claimed.

- Frozen source: `34bda2f53bb8bd31cb7fb8322bf1499dc002d459`.
- Trigger: `9d6411e936844a597a1dd2c87f2bd9c04d879c57`.
- [CI run 38839172392](https://github.com/gbodwin/paper-formalizations/actions/runs/38839172392), job `116775045664`, succeeded on its first attempt.
- [Artifact 12020389413](https://github.com/gbodwin/paper-formalizations/actions/runs/38839172392/artifacts/12020389413): 2,583,872 bytes, 624 uploaded files.
- GitHub/upload-reported ZIP SHA256: `ea5bc1e1afee087c00ba8e9e07577b151599261d829559a985b96774ce1a0637`.

The terminal job log reports 145 sequential commands, 53 project compilations
(52 leaves plus aggregate), 52 individual kernel replays, 24 exact diagnostic
baselines with 44 anchored Lean warnings, 559 actual-owner roots, 20,437 recursively
visited constants, 14 opaque bodies and 46 audit chunks. The gate verified source
snapshots, unique UUIDs, one lock inode, non-overlapping intervals, child reaping,
unchanged tracked source, all dependency pins and the three-axiom allowlist.
All strict compiles and the audit passed. No failed proof invocation occurred in
this combined gate. GitHub Actions' Node deprecation notices are infrastructure
warnings, separate from the 44 Lean diagnostic headers.

`evidence/job-116775045664.log` preserves the decoded terminal job log;
`result-from-job-log.json` extracts its result without implying local execution.
The artifact retains every raw command log, UUID receipt and submitted source,
object/source/toolchain hashes, original recursive TSV and ordered chunks with a
reconstruction manifest. The in-progress log fetch returned 404 before logs were
available; that diagnostic is also preserved.

The connector downloaded the artifact and returned file reference
`file_00000000dbfc81f58c77cd8db1083821`, but the environment could not read its ZIP
bytes: `urllib.error.URLError: <urlopen error Tunnel connection failed: 403 Forbidden>`.
No bypass, credential addition or network/security change was attempted. Thus the
ZIP digest above is reconciled between GitHub artifact metadata and upload logs,
not independently recomputed locally. Independent artifact reconciliation remains
for the reviewer. The prepared `reconcile_artifact.py EXTRACTED_DIRECTORY` checks
manifest bytes/hashes, exact command coverage, source-bound receipts against the
frozen Git source, diagnostic baselines, every singleton replay, exact recursive
closure and chunk reconstruction without running Lean. It was syntax checked,
but could not be exercised on the unavailable ZIP bytes.

Terminal checks show zero active repository CI runs, no local compiler/checker,
and a free universal lock. No local Lean ran during preparation or CI. The
unrelated multi-paper Lean workflow was skipped. Paused for independent review.

Frozen integration source: `34bda2f53bb8bd31cb7fb8322bf1499dc002d459`.
The aggregate includes all 49 paper modules and three imported support modules.
The source-derived union is 52 leaves plus the aggregate. No accepted proof body,
original paper source, earlier evidence, certified branch, or website is changed.
The coverage map is `A Note on Distance-Preserving Graph Sparsification/PROOF_COVERAGE.md`.
It maps the Main Lemma, Theorems 2–12 (including corrected cited 5.2 and proved
subset 10) to actual endpoints and explicit model assumptions. Signed weights,
parallel-edge/self-loop extensions, infinite graphs, runtime claims and the
withdrawn all-pairs claim are excluded. The genuine routing-equality counterexample
is distinguished from the distance/reachability citation correction.

## Prepared gate

`scripts/CombinedPaperCI.py` and `.github/workflows/conditional-plus6.yml` pin the
source above. The one-job workflow uses the existing integration branch and
repository-wide concurrency group. The unrelated Lean job is guarded off on that
branch; the older Slack workflow only triggers on its separate branch. A normal
push is the trigger; no API restriction, credential or security setting is changed.

The runner downloads the official Lean 4.34.0 archive and checks SHA256
`caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b`.
It requires Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, unchanged manifest
SHA256 `615d78a994009475b0e34cd0cd67325b2d863ae37e9f42d8ded7f9d575bf4b2f`,
all nine exact dependency revisions, including mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, and official cache retrieval.
Outputs and dependency checkouts start clean. No default Lake build is used.

The gate compiles each module in dependency order with `-j1 -DautoImplicit=false`,
uses `-DwarningAsError=true` for the strict modules and aggregate, and matches the
24 inherited diagnostic baselines exactly after source-root normalization.
Expected anchored warning headers total 44 (36 original + 8 ConsistentTiebreaking);
hints are not counted again. Each of the 52 leaves is individually replayed with
`leanchecker -v MODULE`; the script verifies singleton replay output. The aggregate
is compiled separately. CombinedAudit inventories all actual owners and recursively
traverses every root's type and body, allowing only propext, Classical.choice and
Quot.sound; unsafe/partial declarations are rejected. Every leaf must occur in the
actual-owner inventory. Full TSVs, ordered chunks and reconstruction hashes are saved.

Every invocation is sequential under the common exclusive lock, with a unique UUID,
submitted source hash/snapshot for compiler/checker operations, child PID, UTC and
monotonic timestamps, and reaping. Raw logs and failed attempts are retained. The
artifact includes source/object/toolchain hashes, inventory, baselines, audit,
receipt reconciliation, commands and an evidence hash manifest. Historical execution
qualifications remain in earlier evidence; this gate does not rewrite them.

No local compiler is run for preparation. Before the trigger, repository-wide active
CI statuses and local compiler processes are checked; local Lean stays off during CI.
The workflow repeats repository-wide activity checks before installing/running Lean.
