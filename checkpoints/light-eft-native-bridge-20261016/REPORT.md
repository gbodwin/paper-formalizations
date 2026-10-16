# Light Edge Fault Tolerant Graph Spanners: native reachability bridge

Tested source: `8dfe637d3661379adf1471c5e6d052321bac3f0a`.
Preserved parent source/evidence: `9f1150416b3f682c57f42058a6075de35b2323fe` / `c21b5fa89ee42e25455c20e1e3a1f1eaff7ea1e2`.
Additive branch: `checkpoint/light-eft-native-bridge-20261016`. Independent review pending; CI skipped. This is a bounded integration checkpoint, not full-paper acceptance.

## Prior review and scope

The user reports independent read-only acceptance of NativeWeightedFaults, with manifests, chunks, receipts, pins and preflight timing reconciled. This records the supplied review, not fresh reviewer execution or CI. All 400 parent proof modules and the previous evidence manifest have been checked unchanged. The parent aggregate gate remains outstanding; adding this module does not claim either the full 400-module parent gate or the resulting 401-module aggregate gate.

The new module is NativeWeightedReachability. It bridges the accepted weighted edge-ID walk semantics to the existing native fault-connectivity and forest-packing contracts. The full weighted multigraph upper bound is not established. Theorem 34 remains unproved, not disproved. There is no runtime claim, website change or work on another paper beyond compiling required unchanged imported support modules.

## Exact mathematical results

`restrictVertexEquiv` and `survivingVertexEquiv` explicitly identify the actual vertex subtype of G with that of its edge restriction and subsequent edge deletion. Both directions preserve the underlying original vertex value. No subdivision, new vertices, change to a vertex-count parameter, or pre-fault identification of parallel edges is used.

`Walk.native_reachable` transforms each custom surviving walk into native reachability in `(G.restrict H).deleteEdges F`. Its induction explicitly separates a self-loop step (equal endpoints) from a nonloop step. A loop contributes only reflexive reachability; a nonloop retains its actual link and edge-ID membership/nonmembership witnesses when constructing native adjacency. No loopless hypothesis is imposed.

`walk_of_native_reachable` performs the reverse full-walk induction. Every native adjacency supplies an actual surviving edge ID, and the induction constructs a custom walk using those IDs. `walk_iff_native_reachable` combines the two directions. It quantifies over every graph G, finite selected set H, finite fault set F and actual endpoints. It includes empty sets, identical endpoints, loops and parallel edges. Faults outside H cause no artificial edge removal.

This is an equivalence of walk existence, not a correspondence preserving weights when the native simple adjacency graph forgets IDs. The weighted walk retains the identities; the native graph forgets them only after restriction and deletion. The previous weighted parallel-edge regression remains unchanged.

`walk_empty_iff_restrict` specializes to the fault-free reachability used by forest-packing contracts. Its graph transport is proved on the fixed original vertex subtype, rather than assuming dependent subtype rewrites.

`faultConnected_restrict_iff` identifies the existing `MultigraphCuts.FaultConnected` contract at any strict threshold k with custom walk existence for all F satisfying `F.card < k`. `faultConnected_succ_iff` proves the precise conversion at k=q+1 to `F.card <= q`, including q=0. `faultConnected_input_iff` specializes to the actual original input IDs. `IsConnectivityPreserver.faultConnected` transports native threshold q+1 from the input to a weighted connectivity preserver using exactly that conversion.

`HasWalkForestPacking` is a finite-edge-ID formulation of the existing contract. `native_forestPacking_iff_walk` proves it equivalent to the actual `EvenSplitting.HasNativeForestPacking` definition. It retains the same native bridge/forest conditions and pairwise edge disjointness. Source demands retain the exact threshold `2*k`, represented by custom survival for every fault set with cardinality strictly below `2*k`; no subtraction or positivity assumption silently changes this threshold. Each packed member's reachability becomes an actual fault-free custom walk. Set-to-finset transport preserves each original selected edge set. The equivalence includes k=0.

These are compatibility theorems. The equivalence does not itself construct an unconditional forest packing or prove a new stretch/lightness upper bound.

## Preflight and execution

Before the first Lean invocation, evidence/preflight.json recorded the clean parent commit, resource capacity, process table, exact parent remote and repository-wide GitHub Actions checks. in_progress, queued, waiting, pending and requested each had zero runs. There was no active Lean/Lake/checker process. Capacity was approximately 23 GiB free disk, 16 GiB memory limit and four CPUs. The sole-worker universal lock remained `/tmp/distance-sparsification-single-compiler.lock`.

The actual forest-packing definition imports an 81-module project closure. These unchanged dependencies were compiled sequentially, including four necessary unchanged LightSpanners support modules. Their exact order is evidence/dependency-order.json. No default multi-paper Lake build, parallel worker, new CI, toolchain shim, dependency update or security-setting change was used. The accepted NativeWeightedFaults object was reused and its hash recorded.

Official Lean is 4.34.0, Release, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b. All nine dependency revisions match the unchanged manifest, including mathlib 5ed2965256430c3649e86755f9576b54eca72435. Toolchain executable, manifest, source and all 83 loaded project object hashes are retained.

Final strict compilation of the new module used `-j1 -DautoImplicit=false -DwarningAsError=true` and emitted no diagnostics. Official `leanchecker -v LightEFTSpanners.NativeWeightedReachability` passed for that individual new module. This is not an individual replay claim for each imported dependency.

The strict recursive audit traversed 726 actual-owner project roots, including 25 declarations owned by the new module, 15784 recursively visited constants and 12 opaque bodies. Types and bodies are traversed, including imported opaque values. Unsafe/partial declarations and unapproved axioms are rejected. Only propext, Classical.choice and Quot.sound were found. Its scope is the loaded 83-module project closure and required mathlib dependencies, not the full paper aggregate.

There are 89 unique source-bound locked receipts: 81 dependency compiles, five strict new-module compile attempts, one individual replay, one strict recursive audit, and one version probe. Four new-module attempts failed before the final successful compile. The first exposed an incorrect nil pattern binder and dependent subtype simplifications; later attempts refined explicit fixed-vertex graph equality proofs and removed rejected unused simp arguments. They are proof elaboration repairs, not mathematical counterexamples. Raw diagnostics, submitted sources and receipts for every failed attempt are preserved. No warning headers occurred; strict-linter errors are retained as failures rather than classified as successful warnings. No literal sorry or new axiom is in the final proof.

Reconciliation checks UUID uniqueness, one lock inode, chronological nonoverlap, reaped children and every submitted snapshot hash. Final compile/replay snapshots match the frozen tested source. The runner records full argv, environment, lock ownership, PIDs, and UTC/monotonic times. UUID attempt folders are authoritative; semantic log names contain the most recent attempt.

## Reproduction and evidence

After coordinating exclusive access, the bounded final checks can be reproduced sequentially:

```
python3 checkpoints/light-eft-native-bridge-20261016/run.py compile
python3 checkpoints/light-eft-native-bridge-20261016/run.py replay
python3 checkpoints/light-eft-native-bridge-20261016/run.py audit
```

`run.py dependencies` compiles the recorded required closure sequentially when it is needed. The runner validates dependency revisions before invoking Lean. `reconcile.py` invokes no Lean process; it checks hashes, pins, receipts, preservation and terminal state, and regenerates derived evidence.

- evidence/source-object-hashes.json: immutable tested source, source hash, 400 preserved source hashes and 83 object hashes.
- evidence/attempts/: source snapshots, receipts and raw logs, including failed attempts.
- evidence/execution-reconciliation.json: sequencing, source binding, failures and warning classification.
- evidence/actual-owner-inventory.tsv and recursive-dependencies.tsv: complete raw audit.
- audit-export/manifest.json: 31 ordered row-aligned chunks and reconstruction SHA256. Concatenate bytes in manifest order with no added separators.
- evidence-sha256.json: packet-wide file sizes and SHA256 hashes.

Terminal reconciliation found no compiler/checker process and a free universal lock. Historical zombie entries are not active workers. Publish this additive checkpoint with CI skipped, preserve all prior work, and pause for independent review. Remaining aggregate, weighted-bound and Theorem 34 obligations are unchanged.
