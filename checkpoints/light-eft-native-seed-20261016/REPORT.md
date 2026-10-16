# Light Edge Fault Tolerant Graph Spanners: native seed-to-forest interface

Tested source: `4a13e4864a819b39b0f9f0bf5a2f953adcb1c86e`.
Preserved parent source/evidence: `8dfe637d3661379adf1471c5e6d052321bac3f0a` / `661d498bd12df7ebb5b8feb2e106a5d82783a29c`.
Additive branch: `checkpoint/light-eft-native-seed-20261016`. CI skipped; independent review pending. No full-paper acceptance is claimed.

## Prior review and preserved scope

The user reports independent read-only acceptance of the native reachability bridge, reconciling 407 manifest entries, 89 receipts and 31 audit chunks. This records that supplied source/log/hash review, not new reviewer execution or CI. All 401 parent mathematical source modules and the parent's evidence manifest have been verified unchanged. Only three additive proof modules and aggregate/checkpoint documentation were added.

Full aggregate validation remains open, including the parent gate and the resulting 404-module aggregate. The full weighted bound and Theorem 34 also remain open. Theorem 34 is unproved, not disproved. No website, optional runtime extension or unrelated paper source was changed.

## Mathematical interface

`NativeSeedDemand.Walk.restore_omitted_fault` proves that restoring a fault on an ID absent from H cannot destroy an H-walk. Its induction uses membership of every traversed ID in H to rule out the omitted ID.

`omitted_edge_survives` considers an actual input edge e omitted by a q-fault connectivity preserver H. Given any fault set F with |F| <= q, it first uses F.erase e. The original e supplies a one-step surviving input walk under this reduced fault set, so the preserver supplies an H-walk. Restoring the fault e is safe because e is absent from H. Thus the endpoints are connected in H after the original F, even when e itself was listed as failed. `omitted_edge_faultConnected` translates this to native threshold q+1 in G.restrict H using the accepted exact budget bridge. Loops and coincident endpoints are allowed.

`NativeEdgeDoubling.doubled G` has vertex type G.vertexSet and edge IDs E x Fin 2. Its actual vertex set is univ by construction, with `doubledVertexEquiv` identifying it with the original actual vertices. The Eulerian theorem's full-vertex hypothesis is therefore proved, not assumed of arbitrary ambient V. There is no subdivision or new vertex insertion. An edge copy (e,i) has exactly e's original endpoints; both copies remain explicitly labeled.

`doubled_degree` proves that every original degree contribution is counted twice. Original loops contribute two to the original native degree and four to the doubled degree. `doubled_even` supplies the Eulerian parity hypothesis.

`doubled_faultConnected` proves the threshold transformation k -> 2*k. For a copied fault set F, it defines the set B of original IDs whose two copies both failed. The product B x Fin 2 is contained in F, giving 2*|B| <= |F| < 2*k and hence |B| < k. An original surviving native walk then lifts by choosing a nonfailed copy at each step. No endpoint pair is collapsed before faults.

`doubled_reachable_project` maps a selected copied walk back to original IDs in Prod.fst '' C. This is a reachability assertion, not a weighted-distance assertion. `projection_congestion` proves that at most two pairwise edge-disjoint copied members can project to any fixed original ID: select one copy from each containing member, then disjointness gives an injection into Fin 2. The proof also permits a single member to contain both copies.

`NativeSeedForests.exists_doubled_projected_forests` applies the existing `exists_native_eulerian_forest_packing` to the doubled actual-vertex graph. It retains the copied forest family C and its disjointness explicitly. Each C member is projected to original IDs. The existing native spanning-forest theorem selects a forest B inside that projection with unchanged reachability; no unproved assertion that arbitrary projection automatically preserves forests is used. These subsets still have congestion at most two.

`exists_seed_forests` specializes this construction to the actual seed G.restrict H, with k=q+1. Its conclusion constructs:

- q+1 pairwise edge-disjoint copied native forests C on the explicitly doubled seed;
- q+1 native forests B on original edge IDs, each contained in H and in Prod.fst '' C for its member;
- at most two memberships among B for every original edge ID;
- an actual fault-free custom H-subset walk in every B member between the endpoints of every omitted actual input edge.

No forest family, Eulerian seed, ambient-fullness hypothesis, final connectivity oracle or weighted upper bound is assumed. The only seed premise is the existing q-fault connectivity-preserver contract. Minimum-weight choice is not required; an attained minimum seed from the earlier module can satisfy this same premise. Empty graphs, unused ambient vertices, q=0, loops, parallel IDs and faults outside selected sets are included. The theorem is an existence/interface result, not a runtime or full weighted-bound result.

## Preflight and official sequential validation

Before any compiler invocation, evidence/preflight.json recorded repository commits, parent remote, resources, process state and repository-wide CI. All five checked statuses (in_progress, queued, waiting, pending, requested) had zero runs. No Lean/Lake/checker process was active. Capacity was approximately 23 GiB free disk, 16 GiB memory limit and four CPUs. The 83 reused project objects matched the accepted parent hashes before invocation; this check is preserved in reused-object-verification.json.

Four missing unchanged dependencies were compiled sequentially: NativePackingVertexTransport, NativeSteinerPackingReduction, NativeIsolatedIslandReduction and NativeEulerianForestPacking. The full required imported project order is recorded separately. No default Lake build, full aggregate build, parallel worker, runtime shim, dependency change, new CI or security-setting change was used.

Official Lean 4.34.0, Release, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, was used. All nine dependencies match lake-manifest.json, including mathlib 5ed2965256430c3649e86755f9576b54eca72435. Source, object, toolchain and dependency hashes/status are preserved.

All three new modules compiled with `-j1 -DautoImplicit=false -DwarningAsError=true`, with zero final diagnostics. Each separately passed official `leanchecker -v MODULE` replay. The strict recursive audit passed: 761 actual-owner project roots, 25 covered declarations owned by the three additions, 15906 recursive constants and 12 opaque bodies. It traverses types and bodies, including imported opaque bodies, and rejects unsafe/partial declarations and nonstandard axioms. Only propext, Classical.choice and Quot.sound occur. This covers the loaded 90-module project closure, not the full paper aggregate.

There are 13 source-bound locked invocations: four dependency compiles, four new-module compile attempts (one failure and three successes), three individual replays, one recursive audit and one version probe. The single Lean failure involved a missing classical decision instance for the congestion predicate and a tuple projection equality needing an explicit change before subst. It is an elaboration repair, not a mathematical blocker or counterexample. Its full raw diagnostics and submitted source remain preserved. There are no warning headers and no literal sorry or added axiom in final source.

Every invocation used `/tmp/distance-sparsification-single-compiler.lock`. Reconciliation verifies unique UUIDs, a single lock inode, chronological nonoverlap, child reaping, all source-snapshot hashes, and final compile/replay hashes against the frozen source. The audit receipt binds the audit source and all three mathematical source files directly. Exact argv/options, environment, PIDs and UTC/monotonic timings are retained in each receipt.

A separate read-only packaging reconciliation initially paired the correct parent manifest with the older checkpoint directory and failed its hash assertion. The copied failing script, raw diagnostic, and an additional failed diagnostic invocation from the copied location are preserved under drafts/ and evidence/reconcile-*.log. Correcting the parent directory made all 401 source-preservation checks and the parent manifest pass. These scripts ran no Lean process and changed no mathematical source or prior evidence.

## Evidence and reproduction

After coordinating exclusive worker access, run the following strictly sequentially for each of NativeSeedDemand, NativeEdgeDoubling and NativeSeedForests in that order:

```
python3 checkpoints/light-eft-native-seed-20261016/run.py compile MODULE
python3 checkpoints/light-eft-native-seed-20261016/run.py replay MODULE
```

Then run `python3 checkpoints/light-eft-native-seed-20261016/run.py audit`. The `dependencies` mode compiles the four recorded missing dependencies when needed. The supervisor never starts a second compiler/checker concurrently. No entire-paper replay claim is made.

- evidence/source-object-hashes.json: frozen source, all three new source hashes, 401 preserved sources and 90 project object hashes.
- evidence/attempts/: authoritative raw logs, source snapshots and lock/PID/timing receipts, including the failed attempt.
- evidence/execution-reconciliation.json: sequencing, hashes, failure and warning classification.
- evidence/actual-owner-inventory.tsv and recursive-dependencies.tsv: complete raw audit.
- audit-export/manifest.json: 32 ordered row-aligned chunks and whole-file reconstruction hash; concatenate bytes without separators.
- evidence-sha256.json: packet-wide file sizes and SHA256 hashes.

Terminal reconciliation found no compiler/checker process and a free common lock. Historical zombie entries are not active workers. Publish only this additive source/evidence checkpoint with CI skipped and pause for independent review. No full aggregate, weighted-bound or Theorem 34 acceptance is claimed.
