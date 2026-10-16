# LightEFT native minimum trees and seed-edge pruning

Tested source: `142be3658cdb3a581cf4a7d9a94fa1ddd981d64f`.
Additive branch: `checkpoint/light-eft-native-pruning-20261016`; source and evidence commits use `[skip ci]`.
Parent evidence: `8201d26884ee408a2d2fa6e0d4b7c14c3180a233`, accepted source `18530baa054f4161e72660765ad400d22d692286`.

This checkpoint constructs native minimum spanning forests, proves the bottleneck cycle property needed for pruning by native cut exchange, and instantiates seed-edge pruning on the actual traced sampled component hosts. It derives **full native weighted-girth exclusion**, preserves sampled candidate IDs and reachability, and controls both retained-tree weight and pruning loss. It awaits independent review. Full aggregate verification, greedy EFT soundness, the native extremal upper bound, the full weighted-spanner theorem and Theorem 34 remain open. No whole-paper completion is claimed.

## Prior review and preservation

The parent reports independent acceptance of the traced cycle-blocking checkpoint above. This records that acceptance as prior source/log/hash reconciliation, not new CI or fresh independent execution. The selected worktree was clean at the expected evidence commit before continuation. All 414 prior proof modules and the entire prior checkpoint evidence manifest were verified unchanged. Only LightEFT source and additive evidence were developed; no completed project, deleted workspace or website was accessed or changed. Existing imported support lemmas were inspected read-only.

## Constructed native minimum forest

`NativeMinimumForest.lean` defines original-ID fault-free reachability, proves endpoint-orientation and whole-walk replacement, and defines `NativeSpans` as a subset preserving every original reachability. The ambient graph need not be connected or nonempty. `NativeForest` requires that removing each retained ID disconnects its endpoints. The bridge theorem reconciles this certificate with mathlib's actual native `Graph.IsBridge`; it does not silently simplify away parallel identities or loops.

`exists_native_minimum_forest` constructs a minimum of actual nonnegative edge-weight sums over the finite powerset of the host. It then minimizes cardinality among equal-weight spanning solutions. The second minimum is essential for zero-weight cycles. If a retained edge had an endpoint detour after deletion, the proved replacement theorem would preserve every old connection; nonnegative weights and weight minimality make deletion weight-neutral or improving, and cardinality minimality gives the contradiction. The result is a genuine native spanning forest with weight at most every spanning competitor. In particular its weight is bounded by a supplied spanning component seed forest.

## Native bottleneck cycle exchange

`NativeForestExchange.lean` proves the edge-deletion component decomposition directly on original-ID walks. Every vertex in the former component remains connected to at least one deleted-edge endpoint. A crossing edge whose endpoints are in that former component restores the deleted edge; whole-walk replacement then restores all old connections.

`native_exchange_weight` applies minimum-weight optimality to that concrete exchanged edge set. A crossing replacement cannot be lighter than the deleted forest edge. Equal weights and zero weights are included.

`native_cycle_maximum_outside` proves the exact bottleneck cycle property used by pruning: **every nonempty edge-simple native closed walk has a maximum-weight original edge ID outside the minimum forest**. It selects a maximum cycle ID. If that ID lies in the forest, the accepted cycle rotation and native bridge cut yield a complementary crossing edge; exchange optimality makes that edge at least as heavy. It is outside the forest and is therefore another maximum, including ties.

This is a direct native proof of the required cycle certificate. It does not assume a bottleneck/MST oracle or a missing pruning contract, and does not need to import a simple-graph bottleneck-path contract into a multigraph. No separate edgewise `HasBottleneckPaths` interface is claimed by this checkpoint. The actual component tree and the needed cycle property are both proved.

## Pruning and full weighted girth

`NativeSeedPruning.exists_native_seed_prune` constructs K and

`R = A \ (seed \ K)`.

K spans A, is a native forest, and is retained in R. Every nonseed ID in A remains in R. R is contained in A and preserves all A-reachability. The chosen K costs no more than any supplied spanning seed T.

For a retained cycle, the bottleneck cycle theorem supplies a maximum-weight ID outside K. Such an ID cannot be a seed ID: it would have been deleted. The already accepted candidate-relative cycle exclusion therefore applies to that maximum, and hence to **every** cycle edge. `NativeWeightedGirthAbove` states this exactly as

`b * w(e) < weight(p)`

for every ID e on every edge-simple closed walk p in R. This is full cycle exclusion, not only exclusion relative to candidates. Loops and distinct parallel two-edge cycles are included: no minimum length or endpoint-pair quotient removes them from the theorem's domain. Zero weights remain allowed.

The generic pruning theorem assumes the previously proved candidate-relative exclusion, then derives full exclusion. The concrete sampled-host endpoint below supplies that premise from the actual traced greedy construction and the accepted sampler. No full-girth conclusion is a premise.

## Actual sampled component and weight budgets

`component_forest_reachable` and `component_forest_spans` build original-ID connectors inside the actual seed component. They justify the spanning competitor used for the minimum; they do not assert that a component tree spans unrelated ambient vertices. `component_selected_tree` proves an actual `IsTree` on the component vertex subtype for the retained native K, using its native bridge certificate and the derived component connectivity.

`exists_pruned_traced_component` starts from the accepted traced sample and constructs all pruning witnesses. It returns:

- a fixed traced blocker family, sample S and original sampled host A;
- K spanning A, native acyclicity, and an actual component-subtype tree;
- R contained in A, with K retained and all sampled candidate IDs retained;
- A and R having the same original reachability;
- `weight(K) <= weight(componentForest)`;
- full `NativeWeightedGirthAbove G R w (t+1)`;
- the sampling/pruning bound `weight(C) <= 4*f*(weight(R) + weight(componentForest))`, with the real casts made explicit in Lean.

The last inequality uses the proved weight-loss bound: A is covered by R plus the original component forest, so pruning loses at most that forest's weight. This supplies an input for the later extremal estimate without asserting that estimate.

Remaining explicit hypotheses are the existing seed forest budget, f > 0, a duplicate-free pairwise weight-ordered candidate list, actual input membership of seed/list IDs, and the chosen actual component. These are the established construction interfaces; there is no unconstructed minimum-tree, pruning, girth or extremal premise. Generic forest/pruning lemmas permit empty/disconnected hosts. Component statements quantify over an actual component, so empty ambient graphs create no spurious chosen root.

## Remaining obligations and scope

The pruned graphs are auxiliary analysis hosts. This checkpoint does not claim that arbitrary seed-edge pruning preserves the EFT stretch property of the final spanner. Complete native greedy EFT soundness, including fault-set normalization and coverage persistence, remains open. A final canonical sorted-list construction interface may still be needed by the complete theorem.

The native extremal weighted-girth upper bound and its aggregation into the full weighted estimate remain open. Existing per-component tree-weight control now supports that work, but no final constant, full native weighted theorem, Theorem 34 or whole-paper completion follows here. The aggregate import list was extended; no aggregate build or paper-wide CI was run.

No false paper statement was found. The previously documented failure of the raw-host full-girth inference is repaired by the actual seed-edge pruning constructed here, not by weakening the cycle domain or assuming the missing conclusion.

## Validation and preserved evidence

Official unmodified Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Release. All nine pinned dependency revisions remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Validation is incremental, reusing 104 hash-reconciled project objects. No clean dependency rebuild, cache download, default Lake build, runtime shim, parallel worker or CI execution occurred.

Each frozen-source module was compiled with `-j1 -DautoImplicit=false -DwarningAsError=true` and individually replayed with official `leanchecker -v MODULE`. Entry points: `python checkpoints/light-eft-native-pruning-20261016/run.py compile LEAF` and `replay LEAF`, for `NativeMinimumForest`, `NativeForestExchange`, and `NativeSeedPruning`; audit/version use `run.py audit` and `run.py version`. All final strict compilations and the audit emitted zero warnings.

The recursive audit passed: 963 actual-owner project roots, 27 declarations owned by the three new modules, 17020 recursively visited constants and 12 opaque bodies. It traverses types and bodies, rejects unsafe/partial dependencies and non-allowlisted axioms, and permits only `propext`, `Classical.choice`, and `Quot.sound`. Exact owners and the imported closure are retained.

Seventeen source-bound locked invocations are preserved, including five failed compilations. Failures were native projection elaboration, a list-lemma argument, strict linter/API/constructor diagnostics, component-tree record construction, and an explicit nonnegativity step in a sum bound. All were proof/elaboration repairs; no mathematical contract was weakened and no warning check was disabled. Failed source snapshots and complete diagnostics remain in their UUID directories. Zero anchored warning headers were emitted; strict-mode errors and hints are classified separately.

`evidence/source-object-hashes.json` binds the frozen source, 107 local object hashes and all 414 unchanged parent modules. `execution-reconciliation.json` verifies 17 distinct UUIDs, submitted-source hashes, one universal lock inode, non-overlapping intervals and reaped children. Every receipt retains exact commands/options, environment search paths, submitted sources, child PID, and UTC/monotonic timestamps. Process/resource preflights precede every invocation.

The original recursive TSV and ordered row-aligned chunks are preserved. `audit-export/manifest.json` gives chunk hashes and the whole-file reconstruction hash; concatenate listed bytes without added separators. `evidence-sha256.json` covers reports, scripts, raw logs, snapshots, receipts, object/source/toolchain hashes, inventories and chunks. `reconcile.py` checks these source/receipt facts without running Lean.

Initial and final-validation public CI checks found zero in-progress, queued, waiting, pending and requested runs. Available disk was approximately 23 GiB and the memory limit 16 GiB. Terminal diagnostics show no compiler/checker and a free common exclusive lock. Source/evidence are published additively with CI skipped, and work pauses for independent review.
