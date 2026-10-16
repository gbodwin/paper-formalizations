# LightEFT native nonnegative extremal bounds

Tested source: `06d44ae091e689695ec0eadf17ff4b9ec9e9cd0b`.
Additive branch: `checkpoint/light-eft-native-extremal-20261016`; source and evidence commits use `[skip ci]`.
Parent evidence: `ccacba78a2943f35221143a6cb852c3a260b4037`, accepted source `142be3658cdb3a581cf4a7d9a94fa1ddd981d64f`.

This bounded checkpoint derives the native extremal estimate on pruned components, including nonnegative weights, actual-ID weight transport, singleton components and zero-total trees. It aggregates component and forest budgets with the additive pruning loss retained as **L+1**. The estimate is proved from the established simple-graph extremal theorem; it is not supplied as a premise. Independent review is pending. Greedy EFT soundness, canonical complete sorted input, the full aggregate build, the final weighted-spanner theorem and Theorem 34 remain open. No whole-paper completion is claimed.

## Prior review and preserved scope

The parent reports independent acceptance of the native pruning checkpoint above, including cut exchange, zero-weight tie-breaking, original-ID preservation and full girth. This records that acceptance as prior source/log/hash reconciliation, not new CI or fresh independent execution. All 417 prior LightEFT proof modules and the prior evidence manifest remain byte-identical.

Development stayed in the LightEFT worktree. The existing extremal theorem requires unchanged imported support modules; their exact source hashes and sequential compilations are recorded below. No other project was developed, no unrelated paper build was run, and no completed/deleted worktree or website was accessed or changed.

## When native simplification is justified

`NativeGirthSimplicity.lean` proves the actual obstruction thresholds using original-ID closed walks:

- A retained loop satisfying full native girth forces `b < 1`; hence `b >= 1` excludes loops.
- Two distinct retained parallel IDs force `b < 2`; hence `b >= 2` excludes parallel IDs.
- At `b >= 2`, the restricted native graph is proved `Graph.Simple` before any endpoint-pair projection is used.

These are uniform threshold guarantees for nonnegative weights; no stronger simplification is assumed below them. The proofs include zero weights and explicitly test both edges of the two-edge cycle. An actual-input singleton/empty-vertex lemma proves the retained ID set empty after loops are excluded. The later component-specific singleton theorem does not require the whole ambient graph to be a singleton.

## Extending the established extremal theorem to zero weights

The established `lightness_le_extremal` theorem ranges over positive actual edge weights and an actual minimum spanning tree. `NonnegativeExtremal.lean` proves the needed extension rather than silently adding positivity to the native theorem.

First, strict nonnegative weighted girth implies every cycle length is strictly greater than the same threshold. A maximum-weight cycle edge exists; if its weight were zero, the strict cycle inequality would contradict the nonnegative cycle sum. Comparing the cycle sum with length times that maximum gives the length bound.

Adding a common positive amount delta to every edge therefore preserves strict girth for all cycles simultaneously. For each delta, the proof constructs a positive-weight minimum spanning tree using the established bottleneck-tree theorem and applies the actual extremal supremum bound. The perturbed minimum tree costs no more than the supplied retained tree. Exact edge-count formulas for the perturbed weight sums and an elementary vanishing-perturbation inequality then give the nonnegative limit.

There is no division by a possibly zero native tree weight. The result `nonnegative_extremal_tree_bound` applies to any retained spanning tree, with arbitrary nonnegative edge weights and `g > 2`. It includes mixed zero/positive edges, zero-total trees and the explicit cardinality-at-most-one case. No native extremal oracle or zero-weight contraction premise is introduced.

## Exact original-ID and component transport

`NativeWeightTransport.lean` constructs `NativeSimpleModel` only after native simplicity is proved. Every retained ID has endpoints in the actual embedded host vertex domain. The endpoint-pair map is injective on retained IDs, and links are equivalent to the assigned unordered endpoint pair. These properties are constructed from native link uniqueness and `Graph.Simple`; they are not assumed without witnesses in the final component theorem.

The projected graph contains exactly the images of retained original IDs. Its weights are pulled back through the unique original ID. `totalWeight_project` proves literal equality between the simple edge-weight sum and the original-ID sum, for both the host and any retained edge subset such as K.

`lift_walk` lifts actual simple walks to native walks, preserving the mapped edge list and exact weight. A simple cycle's distinct edge list gives a native edge-simple closed walk. Full native girth then transports with the identical threshold. Loops and parallel IDs were excluded before this step; neither weights nor fault identities are silently merged.

`native_component_extremal` identifies the projected retained tree with the already proved tree induced on the actual component subtype. The component embeds injectively into the original vertex type, establishing its cardinality bound. It then proves

`weight(R) <= extremalLightness(card V, b) * weight(K)`

for `b > 2`, using the established exact-order monotonicity. The component is not made spanning by adding unrelated isolated vertices. `native_component_singleton_empty` proves R empty for a singleton component. `native_component_zero_tree` proves `weight(R)=0` when `weight(K)=0`; it does not use a ratio convention.

## Fixed-family component bounds and aggregation

`NativeComponentExtremal.lean` uses one **fixed traced blocker family** across every host and component. It derives the sampler's caps/disjointness from that family, constructs the minimum forest and seed pruning, and applies the new native extremal bound. Component-dependent existential blocker choices are not summed as if they were one assignment.

Writing `L = extremalLightness(card V, t+1)`, the proved per-component bound is

`weight(componentCandidates) <= 4*f*(L+1)*weight(componentForest)`.

The +1 is the actual additive pruning loss: the original sampled host is covered by the pruned host plus the component forest. It is never discarded or absorbed without proof into L.

Exact candidate-component partitions avoid duplicate charging within a forest. The sum of component forest weights is bounded by that forest's weight. The accepted native forest congestion budget then yields

`sum_i weight(hostCandidates_i) <= 8*f*(L+1)*weight(H)`.

Finally, `native_candidate_extremal_charge` combines this with the accepted candidate multiplicity theorem. Under `2*f+h <= q+1`, it proves

`h * weight(nativeGreedy ... \ H) <= 8*f*(L+1)*weight(H)`.

No division by h or seed weight is used. Zero-budget boundary cases remain valid. This is a bounded candidate-weight charging result for an explicitly supplied seed forest budget and duplicate-free ordered candidate list, not a completed EFT-spanner construction or final paper theorem.

## Explicit hypotheses and remaining work

The native component bound assumes the retained tree and full-girth certificate produced by the accepted pruning construction. The fixed-family component/aggregate endpoint constructs those witnesses internally from the existing seed forest budget, actual input seed/list membership, a duplicate-free pairwise weight-ordered list, `f > 0`, and `2 < t+1`. The multiplicity endpoint additionally states `2*f+h <= q+1` explicitly. No positivity assumption on individual native weights or on the seed total is hidden.

Complete native greedy EFT soundness, including fault normalization and coverage persistence, is still open. Canonical complete sorted input and final parameter/competition instantiation remain to be integrated. The full aggregate import list was extended but not compiled; no aggregate or paper-wide CI acceptance is claimed. The final weighted theorem and Theorem 34 remain open. No false paper statement was found in this checkpoint.

## Validation and raw evidence

Official unmodified Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Release. All nine dependency pins remain unchanged, including mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

This was incremental verification: 107 prior local objects were hash-reconciled; 59 additional unchanged project dependencies required by `ExtremalLightnessSpectrum` were compiled sequentially. Their submitted snapshots were reconciled against the frozen Git source in `evidence/required-dependency-reconciliation.json`. This is not a default Lake build, unrelated-paper build, dependency update, cache retrieval, clean full build or CI run. The four new modules were individually replayed; the 59 unchanged dependencies were compiled and recursively audited, not individually replayed in this checkpoint.

All four frozen-source modules passed `-j1 -DautoImplicit=false -DwarningAsError=true` and individual official `leanchecker -v MODULE` replay. Entry points are `python checkpoints/light-eft-native-extremal-20261016/run.py compile LEAF` and `replay LEAF`, for `NativeGirthSimplicity`, `NonnegativeExtremal`, `NativeWeightTransport`, and `NativeComponentExtremal`; audit/version use `run.py audit` and `run.py version`. The unchanged support closure uses `run.py dependencies` in stored topological order. No runtime shim or parallel worker was used.

The strict recursive audit passed: 1805 actual-owner project roots, 56 declarations owned by the four new modules, 24337 recursively visited constants and 14 opaque bodies. Types and bodies are traversed, unsafe/partial dependencies and other axioms are rejected, and only `propext`, `Classical.choice`, and `Quot.sound` occur. The expanded count reflects the established extremal theorem's required support closure, not full-paper coverage.

Seventy-nine sequential source-bound locked invocations are preserved, including five failed compilations. Failures were singleton/bottom-graph sum elaboration and a strict linter repair, a list-map lemma argument, and a strict sequencing linter repair. All raw diagnostics and submitted failed sources remain in UUID directories. No mathematical hypothesis was strengthened to repair these failures and no warning check was disabled.

New strict modules and the audit emitted zero warnings. The unchanged dependencies emitted 19 anchored warning headers: SamplingCounting 6, PaddingPositions 2, MainTheorem 1, LightnessBound 1, Blocking 1, EndpointSampling 2, BucketRestriction 3, RetainedGraph 3. Their exact text, source hashes, raw-log hashes and receipts are preserved. Hints and occurrences of the word warning are not counted again; strict-mode errors remain separately classified.

`evidence/source-object-hashes.json` binds the frozen source, 170 local objects and 417 unchanged parent LightEFT modules. `execution-reconciliation.json` verifies all 79 UUIDs/source snapshots, one universal lock inode, non-overlapping intervals and reaped children. Exact commands/options, environment search paths, source hashes/snapshots, child PIDs and UTC/monotonic times are retained. Resource/process preflights precede each invocation.

The original recursive TSV and ordered row-aligned chunks are preserved with a reconstruction hash in `audit-export/manifest.json`; concatenate the listed bytes without separators. `evidence-sha256.json` covers the report, scripts, diagnostics, receipts, snapshots, hashes, inventories and chunks. `reconcile.py` performs read-only source/log/hash checks without Lean execution.

Initial and final-validation public CI checks found zero in-progress, queued, waiting, pending and requested runs. Disk had approximately 23 GiB free and memory limit 16 GiB. Terminal diagnostics show no compiler/checker and a free universal exclusive lock. Source/evidence are published additively with CI skipped, then work pauses for independent review.
