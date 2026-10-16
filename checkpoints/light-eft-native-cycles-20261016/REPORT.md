# LightEFT native insertion blocking: bounded checkpoint

Tested source: `d5b3ab4e82bbac197d20a3eef29e89046f0bdd9a`.
Parent evidence: `99e021fbe4d43d81f38677d0112f31c8146c18d4`, accepted source `28cfc45cf5582ff98aaae94d107749f0f4e4950f`.
Branch: `checkpoint/light-eft-native-cycles-20261016`, commits marked `[skip ci]`.
This is an additive, bounded result awaiting independent review. Full native cycle blocking, full sampled-host weighted girth, the extremal upper bound, full native weighted theorem and Theorem 34 remain open. No whole-paper acceptance is claimed.

## Proved in this checkpoint

`NativeGreedyBlocking.lean` defines a finite tail-first native greedy insertion algorithm on original edge IDs. It skips an already present edge and otherwise inserts precisely when the native fault-tolerant coverage test fails. The list is arbitrary; no sorting, cycle blocking, or girth property is assumed by this construction.

`failed_test_witness` extracts a genuine fault set from the negated insertion test. `nativeGreedy_witness` derives such a witness for every selected nonseed edge by induction on the actual construction. It retains a set A of earlier selected edges, F contained in A, |F| <= f, e outside A, and endpoints for which every surviving A-walk costs more than t*w(e). `nativeWitnessData` fixes these witnesses; its sampling theorem derives selected-blocker membership, the cap and no-self-blocking. These cardinality facts are accompanied by the stronger detour-blocking proof; they are not substituted for it.

`InsertionWitness.detour_lt` handles both endpoint orientations using actual native link uniqueness and walk reversal. `blocks_detour` proves that every earlier detour of weight at most t*w(e) traverses an actual edge ID in F. `clean_cycle_lt` proves

`(t+1)*w(e) < weight(p) + w(e)`

when the complementary detour p uses earlier edges and lies in a host disjoint from F. Zero weights are permitted. No simplification identifies parallel IDs. Empty walks are included: `not_loop` and `nativeGreedy_no_new_loop` exclude newly bought loops. `parallel_blocked` explicitly proves that an earlier parallel ID d with w(d) <= t*w(e) is distinct from e and belongs to F. Thus a surviving short two-edge cycle cannot evade the insertion-time argument by sharing an endpoint pair.

`NativeGreedySampling.lean` applies the accepted component sampling theorem to these *derived* blockers. It retains the component forest, input-ID containment, tree property and factor-4f sampling-weight inequality. Every surviving candidate is loop-free and satisfies the candidate-relative cycle inequality for detours in its witness set A. This is a concrete connection between the new construction and the accepted native host sampler, not a generic blocker assumption.

## Exact scope and remaining proof obligations

The sampling endpoint still explicitly requires: a seed forest budget, f > 0, containment of newly selected IDs in the actual input, and membership of the complementary detour in the witness set A. These are visible in the theorem statement. This checkpoint does not claim the new greedy constructor's complete EFT-spanner soundness or the final weighted estimate.

1. Prove the chronological cycle decomposition: select an appropriate latest inserted candidate on an arbitrary native edge-simple closed walk, rotate/delete it, and prove all complementary edges lie in its earlier set. The current witness specification contains subset information but does not yet export the ranking/trace invariant needed for this step. Transfer weights and original-ID membership, handling loop and parallel two-edge cases explicitly.
2. Connect a nondecreasing insertion order to the candidate weights needed by the full blocking theorem. The current results work for arbitrary lists and establish only insertion-time, candidate-relative blocking.
3. Full weighted girth of the *raw* sampled host does not follow: the maximum-weight edge of a cycle can be a seed edge. The existing simple-graph proof performs additional bottleneck-tree/seed-edge pruning. Construct the corresponding native pruning argument, with original parallel IDs, before invoking any extremal weighted-girth bound.
4. Then prove the native extremal host upper bound and aggregate estimate. No full aggregate or full-paper verification was performed here.

The seed-dominated-cycle issue is a limitation of the tempting intermediate inference, not a newly discovered false paper statement. For example, a seed path of edge weights 100 and 1 plus a candidate of weight 1 passes the insertion test at stretch 3 (the existing detour costs 101; an empty fault witness already suffices). The resulting raw triangle has weight 102, which exceeds 4 times the candidate weight but not 4 times its maximum edge weight 100. Candidate-relative exclusion is therefore insufficient for full weighted girth. This explanatory example is not presented as a Lean-checked counterexample to the paper or as satisfying all final theorem hypotheses.

## Validation and evidence

Official Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Release. All nine dependency revisions remain pinned, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. This was incremental validation using the 98 hash-reconciled cached project objects, not a clean rebuild, cache retrieval, CI run, or default Lake build.

Each new module was compiled from the frozen source with `-j1 -DautoImplicit=false -DwarningAsError=true` and individually replayed with official `leanchecker -v MODULE`. Commands: `python checkpoints/light-eft-native-cycles-20261016/run.py compile MODULE_LEAF`, then `replay MODULE_LEAF`, for `NativeGreedyBlocking` and `NativeGreedySampling`; the final audit uses `run.py audit`, and the version check uses `run.py version`. Every exact argv, environment path, source snapshot/hash, UUID, lock identity, child PID, UTC/monotonic interval and reaping result is retained in `evidence/attempts/*/receipt.json`. No runtime shim is used.

The strict recursive audit visited 888 actual-owner project declarations, including 47 declarations owned by the two new modules, and 16893 recursively reached constants, including 12 opaque bodies. It traverses both types and bodies, rejects unsafe/partial dependencies and permits only `propext`, `Classical.choice`, and `Quot.sound`. The aggregate import list was extended but not compiled; the audit's exact import closure is preserved separately.

Twelve sequential locked invocations are retained, including three failed compilations. The failures were proof-elaboration/tactic syntax, deprecated tactic/lemma names promoted to errors under strict compilation, and a decidable-instance mismatch in the sampled-host wrapper. They were repaired without weakening mathematical contracts or disabling warnings. Final compilations and audit emitted zero warnings; raw failed diagnostics and all submitted sources remain immutable in UUID folders. Anchored diagnostic headers are counted, not occurrences of the word warning in explanatory text.

`evidence/source-object-hashes.json` records the frozen source and 100 imported/new object hashes, and verifies that all 408 parent proof modules remain byte-identical. All prior native-host evidence manifest entries were verified unchanged. `evidence/execution-reconciliation.json` verifies source snapshots, distinct UUIDs, one lock inode, non-overlap, and reaped children. `audit-export/manifest.json` provides ordered row-aligned chunks and the whole-file reconstruction hash; concatenate the listed bytes with no inserted separators. The full original TSV is also retained. `reconcile.py` performs read-only source/log/hash reconciliation and writes derived evidence without running Lean.

The initial response accidentally inspected the completed SCC project; it made no proof changes or compiler invocations there and is not counted as LightEFT progress. This checkpoint contains only LightEFT development. The preserved LightEFT scaffolding and prior preflight were retained. On resumption disk had approximately 23 GiB free, memory limit 16 GiB, and no active Lean/Lake/checker. Public CI status checks returned zero in-progress, queued, waiting, pending and requested runs. Subsequent invocation resource/process preflights are retained. Terminal state is recorded after all children were reaped; the common lock is free. Paused for independent review.
