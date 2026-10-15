# Constructive subset +2 checkpoint — pending independent review

The local official-toolchain validation passes for `IntegerSubsetConstruction G` and `UniformSubsetPlusTwo G 16`, without an unproved construction premise. This is an additive development checkpoint, not whole-paper acceptance, independent acceptance of this checkpoint, or a new CI result.

Tested source commit: **3479c6c51ddf7e970f13cb263128fba8fdd36000**. Its parent is the reviewed supporting-lemma checkpoint **1cb78102a5011809c8da85b23113790bb15935a4**. The final successful source snapshots are byte-identical to the committed sources. The evidence commit only adds reporting/evidence files.

[Prior review record](REVIEW.md) records the user's independent **source/log/hash reconciliation**, not fresh execution of the prior checkpoint. This turn's fresh execution is limited to the four new modules and the combined recursive audit described below.

## Mathematical construction

All four new modules are in `A Note on Distance-Preserving Graph Sparsification/SlackSparsification`, under namespace `SlackSparsification.SubsetPlusTwo`:

| Module | Result |
| --- | --- |
| `SubsetPlusTwoPacking` | `exists_starPacking`: choose a maximum-cardinality finite family of pairwise disjoint size-`d` neighbor sets. An additional residual star would contradict maximality; every residual neighborhood therefore has fewer than `d` vertices. |
| `SubsetPlusTwoConstruction` | `clusteringCertificate_exists`: construct the retained graph from cluster/star edges and residual edges; all certificate fields are proved. |
| `SubsetPlusTwoPurchase` | `captured_prefix`, `captured_suffix`, `purchase_step`: capture bounds actual path-restricted minima; one concrete purchase/rejection step satisfies its demand and emits actual endpoint/cluster labels. |
| `SubsetPlusTwoFold` | `finite_purchase_fold`, `integer_subset_construction`, `uniform_subset_plus_two`: finite ordered-demand fold, amortized edge count, integer budget, and the uniform constant 16. |

Clustering requires only `0 < d`. A cluster of `d` vertices contributes at most `d²` edges: each member offers its center plus its other cluster members, filtered to original edges. Disjointness gives `q*d ≤ n`, so all cluster/star edges cost at most `n*d`. Residual edges are an undirected image of residual neighbor sets, costing at most `n*d`. Thus the certificate satisfies `base.edgeFinset.card ≤ 2*n*d`. The universal construction covers empty vertex types and `d > n`; it does not choose a center from an empty type unless there is a nonempty cluster requiring one.

The fold processes the finite list `(S ×ˢ S).toList`. Its recursively defined states satisfy `base ≤ H_i ≤ G` and `H_i ≤ H_(i+1)`. For a reachable, distinct-endpoint demand, the chosen walk is genuinely shortest. A purchase retains all its edges, uses at most the count of missing indexed steps, and captures both path-restricted minima. Rejection uses the prior verified common-cluster routing lemma. It never equates a restricted minimum with a global cluster distance.

The diagonal is handled first with no purchase or charge. Unreachable demands also require neither. For distinct endpoints `s ≠ t`, `{s} × BL` and `{t} × BR` are disjoint, so the actual label cardinality is exactly `|BL|+|BR|`; coincident endpoints cannot be double counted. Every charged label strictly improves and its post-distance is at most global distance +2. The existing graph-level three-improvement theorem handles infinite global distances explicitly. The actual label universe is `S × clusters`, and total purchase cost is at most `6*|S|*q`.

Edge increments telescope to `|base edges| + 6*|S|*q`. Monotonicity preserves every earlier satisfied demand. With `|S| ≤ d²` and `qd ≤ n`, the integer budget is `8nd`. The prior verified ceiling/square-root reduction yields **`UniformSubsetPlusTwo G 16`**.

Remaining mathematical hypotheses: a finite vertex type with equality decidable and a simple undirected unweighted graph. The integer intermediate uses positive `d` and `|S| ≤ d²`; the final uniform theorem has neither parameter nor construction assumption and does not require connectedness. Classical choice is used. This proves existence, not a formal polynomial-time algorithm.

The accepted conditional +6 source `d0f9ee2364bf4a5aaa7e0ca4da48216e42bbc63e`, all its evidence, and all prior checkpoint files remain unchanged. No +6 module, aggregate import, certified branch, or website was edited. No claim is made here about other paper statements or whole-paper completion. Integrating the new endpoint into accepted source and independently reviewing it remain separate steps.

## Exact local validation

Official unmodified Lean **4.34.0**, commit **293d5d0c0c3f3dded4688b3ccd6a33939ac5102b**; Lake **5.0.0-src+293d5d0**. Mathlib **5ed2965256430c3649e86755f9576b54eca72435**. All nine dependency checkouts still match `lake-manifest.json` and are clean. The official toolchain provenance/archive comparison remains the previously preserved evidence; this turn records fresh version output and executable hashes, not a new release-archive extraction.

[Source/object hashes](source-object-hashes.json), [dependency checks](dependencies.json), [toolchain hashes](toolchain-binary-hashes.json), and [environment diagnostics](environment.json) are preserved. The environment reconnect showed 23 GiB free disk, a 16 GiB cgroup memory limit, and four CPU quota cores. No parallel worker was used.

Every new compilation used:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -DautoImplicit=false -DwarningAsError=true --root=<paper-root> -o <module.olean> <module.lean>
```

The exact absolute arguments, `LEAN_PATH`, elapsed time, exit status, source SHA256, source snapshot, and raw diagnostics are retained for **all 12 attempts**, including seven failed attempts. Final successful attempts:

| Module | Final attempt | Compilation | Individual official kernel replay |
| --- | --- | --- | --- |
| Packing | 002 | exit 0; no diagnostics | exit 0 |
| Construction | 005 | exit 0; no diagnostics | exit 0 |
| Purchase | 009 | exit 0; no diagnostics | exit 0 |
| Fold | 012 | exit 0; no diagnostics | exit 0 |

Attempt 011 also passed; 012 recompiles the final comment-only correction. The failures were elaboration/API/name/definitional-equality issues and one unused-simp-argument linter finding (attempt 010, promoted to error). They were fixed without suppressing lints, adding axioms, or using `sorry`. Final compilation produces **zero warnings**. The 36 inherited warnings belong to the previously accepted validation; this turn did not rebuild those modules or reclassify them as new warnings.

Each replay command was exactly `lake env leanchecker -v SlackSparsification.SubsetPlusTwo<MODULE>`, run sequentially and checked to select one exact leaf module. Each raw output is exactly its `replaying ...` line. No default `lake build` was run.

The combined audit was:

```text
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true "A Note on Distance-Preserving Graph Sparsification/verification/SubsetPlusTwoConstructionAudit.lean"
```

Result: **131 actual-owner declarations across ten modules** (95 prior supporting declarations plus **36 newly owned declarations**), **14,320 recursive constants**, **13 opaque bodies**. It recursively inspects declaration types and definition/theorem/opaque bodies, including private declarations; it rejects unsafe/partial constants and disallowed axioms. The only axioms are **`propext`, `Classical.choice`, `Quot.sound`**. The raw audit calls all ten selected modules “new”; [audit coverage](audit-coverage.json) gives per-module counts and this report distinguishes the four actually added modules.

[Raw evidence](evidence/) includes inventory, import closure, individual replay logs, all compilation attempts, and recursive dependency TSV. [Chunk manifest](evidence/dependency-chunk-manifest.json) makes the large TSV readable in pieces; concatenating chunks in manifest order exactly reconstructs the raw bytes and SHA256. [Preservation checks](preservation.json) verify prior source/object manifest hashes, additive-only source changes, and the clean certified checkout at `dc376e8efac8c1bc236abbe68d296060d7ba4142`.

## Handoff and CI

Branch: `checkpoint/subset-plus2-cgk13-20261015`. Both additive commits carry `[skip ci]`; existing workflow guards already exclude this branch from the general multi-paper job, and the project-specific gate only listens on the integration branch. No workflow trigger or security setting was changed. No CI is requested by this checkpoint.

The reviewer should use the exact source commit above and reconcile final source snapshots/object hashes before any coordinated fresh sequential execution. All local compiler/checker processes have exited. No genuine environment or proof blocker remains for the two requested theorem endpoints; independent review and any future CI remain pending.
