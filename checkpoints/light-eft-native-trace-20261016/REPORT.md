# LightEFT traced native cycle blocking

Tested source: `18530baa054f4161e72660765ad400d22d692286`.
Additive branch: `checkpoint/light-eft-native-trace-20261016`; source and evidence commits use `[skip ci]`.
Parent evidence: `338f52aaed476be9afda2922568301dffe61e1f1`, accepted source `d5b3ab4e82bbac197d20a3eef29e89046f0bdd9a`.

This checkpoint proves chronological cycle blocking and removes the earlier-detour premise from candidate-relative sampled-host cycle exclusion. It does **not** prove full weighted girth, native seed-edge pruning, the extremal upper bound, complete greedy EFT soundness, the full native weighted theorem or Theorem 34. It awaits independent review; no whole-paper claim is made.

## Prior review and preserved scope

The parent reports independent acceptance of the bounded insertion-time blocking checkpoint above. This records that review as source/log/hash reconciliation, not new CI or fresh independent execution. All 410 prior proof modules and the prior evidence manifest remain byte-identical. This turn worked only on Light Edge Fault Tolerant Graph Spanners. No SCC project, other completed paper, deleted workspace or website was accessed or changed.

## Trace and input containment

`NativeGreedyTrace.lean` introduces `InsertionTrace`, recording the actual input decomposition

`es = tr.preEdges ++ e :: tr.postEdges`.

The earlier selected set is definitionally `nativeGreedy ... tr.postEdges`, not a freely chosen subset. The trace records absence of e and failure of its native coverage test at that exact state. `rank` is the length of `postEdges`, the number of already processed IDs in the tail-first construction; `rank_lt` bounds it by the input length. `seed_subset` puts the entire seed in that earlier state, `earlier_subset` puts that state in the final output, and `witness` derives the fault witness there.

`exists_latest_trace` works for any finite subset C of the selected output containing a nonseed edge. It selects an actual latest insertion e, proves `C.erase e` was already selected at that point, and bounds every nonseed C-edge's weight by w(e). The explicit input list is pairwise nonincreasing, hence insertion order is nondecreasing. The proof follows the actual insertion/skipping decisions. No chronology or complementary-edge membership is assumed.

`nativeGreedy_subset_input` proves that the output is contained in the union of the seed and listed IDs. `nativeGreedy_input_containment` then derives actual input-edge containment from seed/list input conditions, including empty lists. This closes the earlier containment obligation under the ordinary, explicit input-domain hypotheses. It does not assert complete EFT-spanner soundness of the greedy algorithm.

## Original-ID rotation and global blocking

`NativeCycleRotation.lean` proves exact edge-list and weight preservation for transfers between selected sets. It splits a walk at an occurrence of an original ID, then rotates a closed edge-simple walk at e and removes that edge. The complementary walk runs from the second endpoint back to the first. Its edge list is duplicate-free and contains exactly the original cycle IDs other than e; its weight plus w(e) is the original weight.

There is no minimum-cycle-length hypothesis and no vertex-pair edge identification. A loop produces an empty complement; a two-edge cycle with distinct parallel IDs produces a one-edge complement. Arbitrary edge-simple closed trails are covered, including those with repeated vertices. All arguments use actual walks and exact weights, not an equality between path-restricted and global distance or an assumption that unreachable distances are finite.

`NativeCycleBlocking.latest_cycle_complement` combines the finite-set latest trace with this rotation. It constructs the complementary walk in the exact earlier selected set, proves seed containment there, retains exact ID membership and weight, and proves the required weight ordering against every nonseed cycle edge.

For duplicate-free input lists, `InsertionTrace.same_earlier` proves that two traces for the same ID refer to the same earlier state. `exists_traced_blockers` chooses one fixed fault set per candidate from actual trace witnesses, with empty blockers outside the newly selected set. The family is fixed before considering any cycle; blockers are not chosen anew for each cycle.

`TracedBlockers.blocks_cycle` proves that any original-ID edge-simple closed walk of weight at most `(t+1)*w(d)`, where d is a nonseed cycle edge, contains a pair (e,z) with e nonseed and z in block(e). It uses the latest candidate and transfers the fixed witness to that exact earlier state by trace uniqueness. `TracedBlockers.sampling` derives fault caps, no self-blocking and selected-blocker membership for this same family.

## Sampled component endpoint

`NativeTracedSampling.exists_traced_component_sample` derives a fixed traced blocker family and applies the accepted component sampler. The result retains its component seed forest, actual input-ID containment, component tree property and factor-4f sampling-weight bound. For every edge-simple closed walk p in the sampled host and every nonseed edge d on it, it proves

`(t+1)*w(d) < weight(p)`.

The old earlier-detour premise is gone. The proof derives disjointness from the sampled survivor construction, transfers the entire walk to the final selected graph, and contradicts the fixed family's global cycle-blocking theorem.

Remaining explicit hypotheses are the existing seed forest budget, positive sampling fault parameter f, a duplicate-free pairwise weight-ordered candidate list, actual input membership of seed/list IDs, and edge-simplicity of the tested closed walk. Nonnegative finite weights, including zero, are retained. The theorem does not suppose full girth, an extremal estimate, or a cycle-blocking certificate as an unexplained premise.

## Remaining obligations

1. Construct native seed-edge pruning, with a suitable native bottleneck spanning tree and explicit original IDs. Candidate-relative exclusion does not imply full weighted girth if a seed edge dominates a cycle. The prior report's qualification remains in force; it is not a false-paper-statement claim.
2. Prove complete EFT soundness for the finite native greedy constructor, including fault-set normalization and coverage persistence. The new input containment theorem alone is not spanner soundness.
3. Build any final canonical sorted candidate-list interface needed by the full construction. This checkpoint proves theorems for an explicit duplicate-free ordered list.
4. Prove the native extremal host upper bound after legitimate pruning, then the aggregate/full native weighted theorem and Theorem 34. No full-paper or aggregate acceptance follows from this checkpoint.

## Validation and raw evidence

Official unmodified Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Release. All nine pinned dependency revisions are unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. This is incremental verification using 100 hash-reconciled cached project objects, not a clean build, cache download, CI execution or default Lake build.

Each of the four frozen-source modules was compiled with `-j1 -DautoImplicit=false -DwarningAsError=true`, then individually replayed with official `leanchecker -v MODULE`. Entry points are `python checkpoints/light-eft-native-trace-20261016/run.py compile LEAF` and `replay LEAF`, for `NativeGreedyTrace`, `NativeCycleRotation`, `NativeCycleBlocking`, and `NativeTracedSampling`; audit/version use `run.py audit` and `run.py version`. Final strict compilations and audit emitted zero warnings. The aggregate import list was extended but the aggregate itself was not compiled.

The strict recursive audit passed: 936 actual-owner project roots, 48 declarations owned by the four new modules, 16967 recursively visited constants and 12 opaque bodies. Types and bodies are traversed; unsafe/partial declarations and non-allowlisted axioms are rejected. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The exact inventory and loaded import closure are retained.

Seventeen sequential source-bound locked invocations are preserved, including two failed compilations. The first failure involved the reserved field name `prefix`, local-definition simplification and a strict linter diagnostic. The second exposed dependent rewriting of a trace's indexed input list. These were proof/elaboration repairs, not mathematical assumption changes or paper counterexamples. Every failed submitted source and complete raw diagnostic remains in its UUID directory. Zero anchored warning headers were emitted; strict-mode errors and hints are not counted as separate warnings.

`evidence/source-object-hashes.json` binds frozen source, 104 local object hashes and all 410 unchanged parent modules. `execution-reconciliation.json` verifies all 17 source snapshots, unique attempt IDs, the common lock inode, non-overlapping intervals and reaped children. Every receipt retains exact argv/options, submitted source hashes, environment search paths, child PID and UTC/monotonic times. No compiler/runtime shim or parallel worker was used.

Ordered row-aligned audit chunks and their reconstruction SHA256 are in `audit-export/manifest.json`; concatenate the listed bytes with no inserted separators. The original TSV, raw logs, failed attempts, inventories, hashes, receipts and scripts are covered by `evidence-sha256.json`. `reconcile.py` performs read-only hash/source/receipt reconciliation without Lean execution.

Initial and final-validation CI checks found zero in-progress, queued, waiting, pending or requested runs. Resource/process preflights precede every invocation. Available disk was approximately 23 GiB and the memory limit 16 GiB. Terminal state records no compiler/checker and a free universal exclusive lock. Source and evidence are pushed additively with CI skipped, then work pauses for independent review.
