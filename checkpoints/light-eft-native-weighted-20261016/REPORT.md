# Light Edge Fault Tolerant Graph Spanners: native weighted fault semantics

Tested source: `9f1150416b3f682c57f42058a6075de35b2323fe`.
Preserved parent evidence/source: `00a732e31cb1a5e7bd1f70e376d9bcbaf1a7b5f4` / `7e4c0a730d13655fc75a4629dd4056a21a9a7cce`.
Additive branch: `checkpoint/light-eft-native-weighted-20261016`. CI skipped; independent review pending. This is not whole-paper acceptance.

## Review and preflight

The user reports independent acceptance of the bounded threshold theorem and its local evidence. This records that supplied review as source/log/hash reconciliation, not new reviewer execution or CI. All 399 prior mathematical modules and the previous evidence manifest have been verified unchanged. The original `light-eft-spanners-checkpoints` remote remains at faaaad5a31de3fef117f023154405ea21f2af1aa, and the prior additive branch remains at 00a732e31cb1a5e7bd1f70e376d9bcbaf1a7b5f4.

Before the first invocation, evidence/preflight.json and remote-preflight.txt recorded repository state, capacity, processes and GitHub CI checks. All five statuses (in_progress, queued, waiting, pending, requested) had zero runs. Capacity was 23 GiB disk free, 16 GiB memory limit and four CPUs. No compiler/checker was active. The read-only shell preflight returned 1 because its final AGENTS.md search found no file; resource and repository checks succeeded. No parallel worker or compiler/checker was used. The universal exclusive lock is `/tmp/distance-sparsification-single-compiler.lock`.

## Mathematical contract

`NativeWeightedFaults.lean` uses the existing mathlib `Graph V E` directly. A walk is indexed by the graph's actual vertex subtype and records every traversed original edge ID, its actual `IsLink` proof, membership in the retained edge set H, and nonmembership in the fault set F. No parallel-edge collapse, graph subdivision or vertex replacement occurs. Loops are permitted.

`surviving_link_iff` proves the step predicate agrees exactly with native `G.restrict H` followed by `deleteEdges F`. Fault sets are arbitrary finite subsets of the original E, including faults outside H. `Walk.weight` sums the weights of traversed edge IDs, counting repetitions. Weights are finite nonnegative reals encoded as NNReal; zero weights are allowed. This is not a semantics for negative weights.

`distance` is an ENNReal infimum over surviving walks. `distance_eq_top_iff` proves that infinity occurs exactly when there is no surviving walk, rather than assigning a finite default to unreachable pairs.

`edgewise_replacement` proves by induction that replacing every surviving original edge with an H-walk of weight at most t times that edge's weight yields an H-walk of weight at most t times every surviving original walk's weight. Concatenation and weight addition are proved explicitly. `IsEFTSpanner.distance_le` derives extended-distance stretch for t != 0; the nonzero condition handles unreachable demands without an invalid 0*infinity inference. `native_edgewise_distance` specializes this to G's actual original edge IDs. It does not assume a supplied final distance inequality. Reachability preservation follows and is equivalent in both directions because H is a subset of the input IDs.

`exists_minimum_preserver` minimizes total edge weight over the finite powerset of the original finite edge set. The entire input is always a feasible connectivity preserver, so the minimum is attained even for empty inputs, disconnected graphs and zero weights. `minimumPreserverWeight_attained` proves attainment and the lower-bound property against every feasible J. `native_minimum_attained` specializes to the actual edge set of a graph with finite E and proves the minimizing edges are actual input IDs. The more general finite-set theorem does not require finite V or finite E. No denominator positivity or lightness ratio is claimed.

Two symbolic parallel-edge regressions quantify over distinct e0,e1 with the same endpoints. `parallel_delete_exact` proves deletion of {e0} removes e0 but leaves e1 linking those original endpoints. `parallel_identity_survives` produces the surviving walk and proves its weight is exactly w(e1). These tests do not replace the two edges by an endpoint pair before deletion.

The remaining weighted-multigraph upper-bound construction and its lightness analysis are not discharged by this semantic layer. No polynomial runtime or vertex-dependent cardinality bound is asserted here. Theorem 34 remains unproved, not disproved; this checkpoint supplies no new counterexample or paper-false claim. No other paper or website was modified.

## Validation and preserved attempts

Official Lean 4.34.0, Release, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b. All nine dependency revisions match the unchanged lake-manifest.json; mathlib is 5ed2965256430c3649e86755f9576b54eca72435. Dependency status and toolchain hashes are saved. There are no runtime shims or security/network-setting changes.

The final module compiles with `-j1 -DautoImplicit=false -DwarningAsError=true` and zero diagnostics. Official `leanchecker -v LightEFTSpanners.NativeWeightedFaults` passes on the final object. The recursive audit passes with 78 actual-owner roots (including generated inductive support), 10116 recursively visited constants and 12 opaque bodies. It traverses types and bodies, rejects unsafe/partial declarations and unexpected axioms, and finds only `propext`, `Classical.choice`, and `Quot.sound`. The audit includes this new module and its mathlib closure; it does not claim full validation of the now-400-module aggregate. The new module imports no other paper's proof modules.

The ten UUID receipts comprise five strict compilation attempts (three failures, two successes), two individual kernel replays (before and after the runtime-wrapper correction), two recursive audits (one failure, one success), and one official version probe. All invocations are sequential and source-bound, with exact commands/options, LEAN_PATH, lock identity, PIDs, timing, raw logs and submitted-source snapshots. Reconciliation verifies UUID uniqueness, one lock inode, nonoverlap, source hashes and reaped children. Final compilation and replay source hashes match the frozen tested source. No warning headers occur; strict-linter failures remain classified as failed attempts rather than silently counted as successful warnings.

The three compilation failures were notation scope/dependent recursion elaboration, an equality orientation in the infinity proof, and missing classical finite-subtype instances. Compiler-generated error recovery mentioning sorry is retained in raw failures; no literal sorry or added axiom is in the final source.

The first audit rejected a generated partial runtime wrapper `Walk.append._unsafe_rec`, after compilation and kernel replay had passed. The mathematical recursive operations weight/append/mono were marked noncomputable to omit runtime code wrappers. The audit rules were not weakened. Final compilation, audit and individual replay all passed afterward. Both source commits and every failed attempt are retained.

Reproduction commands, each invoking the established exclusive-lock supervisor:

```
python3 checkpoints/light-eft-native-weighted-20261016/run.py compile
python3 checkpoints/light-eft-native-weighted-20261016/run.py replay
python3 checkpoints/light-eft-native-weighted-20261016/run.py audit
```

Run these sequentially only after coordinating exclusive worker access. No default lake build was run. `reconcile.py` performs source/evidence checks without invoking Lean; it regenerates derived metadata and terminal-state evidence.

## Evidence and handoff

- `evidence/source-object-hashes.json`: frozen source, source SHA256, final object SHA256 and preserved parent count.
- `evidence/attempts/*/receipt.json`, `raw.log` and SHA-named source snapshots: authoritative invocation evidence, including all failures.
- `evidence/execution-reconciliation.json`: sequencing, source bindings, failed/superseded attempts and warning classification.
- `evidence/recursive-dependencies.tsv` and `actual-owner-inventory.tsv`: raw complete audit.
- `audit-export/manifest.json`: hashes and ordered reconstruction of 19 row-aligned TSV chunks; concatenate raw bytes without separators.
- `evidence-sha256.json`: packet-wide file sizes and hashes.

Terminal checks show no Lean/Lake/checker process and a free universal lock. The historical defunct python process is not a running worker. Preserve all partials, push only this additive checkpoint with CI skipped, and pause for independent review. The checkpoint proves the listed semantic and replacement contracts only.
