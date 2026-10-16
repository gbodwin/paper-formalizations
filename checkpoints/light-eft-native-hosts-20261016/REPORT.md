# Light Edge Fault Tolerant Graph Spanners: component assignments and sampled native hosts

Tested source: `28cfc45cf5582ff98aaae94d107749f0f4e4950f`.
Preserved parent source/evidence: `6c8aaf1d6415589a8d9cfe904fe107fe9acd05ec` / `c108837c01ecb9971d3205c67f066bb9ddeaee87`.
Additive branch: `checkpoint/light-eft-native-hosts-20261016`. CI skipped; independent review pending. No whole-paper acceptance is claimed.

## Prior review and bounded scope

The user reports independent read-only acceptance of NativeSeedBudget, with all packet bytes and receipts reconciled. This records the supplied review, not fresh reviewer execution or CI. All 405 parent proof modules and the preceding evidence manifest have been verified unchanged. Three additive modules are included; no unrelated source or website was edited.

This checkpoint constructs native candidate-to-host assignments and their component partition, proves weighted multiplicity, and advances the per-host argument through an actual blocker-free sampled host and its sampling-weight estimate. It does not prove the remaining host-weight-to-tree-weight upper estimate. Full aggregate validation (including the earlier 404-module gate and now-408-module aggregate), the full weighted-multigraph bound and Theorem 34 remain outstanding. Theorem 34 is unproved, not disproved.

## Assignments and component accounting

`NativeCandidateAssignments.hostCandidates U T block i` explicitly assigns each original candidate edge ID e to every forest T_i disjoint from its supplied blocker set block(e). Nothing is identified with an unordered endpoint pair.

`candidate_multiplicity` uses the existing arbitrary-ID host count: blockers of size at most f, congestion two, and `2*f+h <= |I|` yield at least h assigned hosts for each candidate. `candidate_weight_multiplicity` proves the corresponding weighted charging multiplicity by the original-ID incidence identity. `native_assignment_properties` instantiates these facts for the constructed q+1 seed forests with the explicit condition `2*f+h <= q+1`, and retains U as a subset of actual input IDs outside H.

`componentCandidates` filters a host's assigned candidates by the existence of actual endpoints inside a specified connected component. For each assigned actual candidate, the accepted seed forest's genuine walk places both endpoints in one component. Native edge endpoint uniqueness proves that this component is unique for that ID, including loops and parallel IDs. No ID is counted in two component bins within one host forest. `sum_component_candidate_weights` proves that the component candidate weights sum exactly to the host forest's assigned candidate weight.

`host_component_tree` derives a genuine tree on each component's own vertex subtype from the native forest bridge condition. It does not assert that a possibly disconnected forest is one spanning tree on all original vertices.

## Native per-component sampling step

`NativeHostSampling.componentForest` retains the original forest IDs internal to a component. `component_forest_adjacency` explicitly proves that these IDs represent the adjacency of the actual component tree, on the component vertex subtype. Candidate and forest weights remain functions of the original E IDs. `sum_component_forest_weights_le` proves that component seed weights sum to at most the original forest weight; no seed ID is duplicated between components.

For each component's candidate set K, `exists_sampled_component_host` applies the existing finite arbitrary-ID weighted sampling theorem to explicit blocker sets. Its assumptions are f>0, |block(e)| <= f, and e not in block(e) for the candidate IDs. It constructs a concrete S subset K and the native selected edge set

`R = componentForest union surviving K block S`.

It proves that R consists of actual original input IDs, retains the entire original-ID component forest, and every selected edge has both endpoints inside that actual component. The component tree property is included. Every retained candidate's blocker set is disjoint from R. Finally it proves the sampling-weight inequality

`weight(K) <= 4*f * weight(R)`.

The host is the actual native restriction G.restrict R. This result is not a weight bound inferred from an assumed final estimate. It constructs the finite sample and derives its weight estimate from the retained sampling theorem; all edges retain their original identity and weight.

This advances the per-host argument through the sampled-host construction and sampling-weight step only. Cardinality caps and no-self-blocking do not establish a native cycle-blocking property. A native cycle-blocking/high-girth argument, followed by the required extremal upper bound on weight(R) in terms of the component-tree weight, remains open. No such assertion is inserted as a hypothesis and then presented as a completed per-host bound. The existing `spanning_host_family_bound` for spanning simple trees on Sym2 edge IDs is not invoked on disconnected native forests or arbitrary native candidate IDs.

## Denominator positivity is separate

`NativeSeedPositivity.preserver_weight_pos` proves positive preserver weight when every actual input edge has strictly positive weight and there is an actual nonloop input edge (distinct actual endpoints). Connectivity preservation at the empty fault set yields a seed walk with at least one actual positive-weight edge, whose weight is bounded by the seed sum.

`minimum_weight_pos_of_nonloop` instantiates this with the attained minimum preserver. These explicit nonloop/positive-edge assumptions are not imposed on the earlier zero-valid budget theorems. Empty inputs, loop-only inputs or zero edge weights are not silently assigned positive denominators. The sampling denominator 4*f uses its own explicit f>0 assumption and never divides by seed weight. No final lightness ratio is asserted.

## Preflight and sequential validation

Before any invocation, evidence/preflight.json recorded the clean parent and remote, capacity, processes and repository-wide CI checks. All five checked active statuses (in_progress, queued, waiting, pending, requested) had zero runs. No Lean/Lake/checker process was active. Resources were approximately 23 GiB free disk, 16 GiB memory limit and four CPUs. All 92 reused objects matched accepted hashes before invoking Lean.

Three required unchanged dependencies were compiled sequentially: LightSpanners.FiniteSampling, LightEFTSpanners.BlockerSampling and LightEFTSpanners.WeightedSampling. These are imported support for this paper's sampling step, not work on a separate paper. No default Lake build, full aggregate build, new CI, parallel worker, dependency update, runtime shim or security-setting change was used.

Official Lean 4.34.0, Release, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, was used. All nine dependency revisions match the unchanged lake-manifest.json; mathlib is 5ed2965256430c3649e86755f9576b54eca72435. Toolchain hashes, pins/status, source hashes and all 98 loaded project object hashes are retained.

All three final modules compiled with `-j1 -DautoImplicit=false -DwarningAsError=true`, emitting zero diagnostics. Each separately passed official `leanchecker -v MODULE`. The strict recursive audit passed: 841 actual-owner project roots, 22 covered declarations owned by the additions, 16840 recursively visited constants and 12 opaque bodies. It traverses types and bodies, including imported opaque bodies, and rejects unsafe/partial declarations and unapproved axioms. Only propext, Classical.choice and Quot.sound occur. This is the loaded 98-module project closure, not full aggregate validation.

There are 15 unique source-bound invocations: three dependency compiles, seven new-module compilation attempts, three individual replays, one strict audit and one version probe. Two compilation attempts failed: finite component existential predicates exposed differing inferred decision instances, and a positivity proof used the wrong zero_le application form. Membership lemmas and an explicit positivity proof repaired these without changing mathematical hypotheses. Intermediate successful source snapshots before the final combined assignment/accounting additions are also retained. There are no warning headers. Raw failed diagnostics and submitted sources remain preserved; no literal sorry or new axiom is in final source.

All invocations used the universal exclusive lock `/tmp/distance-sparsification-single-compiler.lock`. Reconciliation verifies unique UUIDs, one lock inode, nonoverlap, reaped children and every source-snapshot hash. Final compile/replay snapshots and the audit's directly submitted sources match the frozen source. Exact commands, options, LEAN_PATH, PIDs and UTC/monotonic timing are in the receipts.

## Evidence and reproduction

After coordinating exclusive access, compile and replay NativeCandidateAssignments, NativeSeedPositivity and NativeHostSampling in that order, strictly sequentially:

```
python3 checkpoints/light-eft-native-hosts-20261016/run.py compile MODULE
python3 checkpoints/light-eft-native-hosts-20261016/run.py replay MODULE
```

Then run `python3 checkpoints/light-eft-native-hosts-20261016/run.py audit`. The dependencies mode builds the three recorded missing dependencies when needed. The accepted imported closure is reused. `reconcile.py` runs no Lean process; it checks preservation, pins, receipts and hashes and regenerates derived evidence.

- evidence/source-object-hashes.json: frozen source, all three new hashes, 405 preserved source hashes and 98 project object hashes.
- evidence/attempts/: authoritative raw logs, submitted source snapshots and source-bound lock/PID/timing receipts, including failed attempts.
- evidence/execution-reconciliation.json: sequencing, failures, superseded snapshots and warning-header count.
- evidence/actual-owner-inventory.tsv and recursive-dependencies.tsv: complete raw audit.
- audit-export/manifest.json: 34 ordered row-aligned chunks and whole-file reconstruction hash; concatenate bytes without separators.
- evidence-sha256.json: packet-wide sizes and SHA256 hashes.

Terminal checks show no compiler/checker process and a free common lock. Publish this bounded source/evidence checkpoint with CI skipped, then pause for independent review. The remaining native high-girth/host-upper-weight step is explicitly open, alongside aggregate validation, the full weighted bound and Theorem 34.
