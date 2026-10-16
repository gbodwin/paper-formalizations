# Light Edge Fault Tolerant Graph Spanners: weighted minimum-seed budget

Tested source: `6c8aaf1d6415589a8d9cfe904fe107fe9acd05ec`.
Preserved parent source/evidence: `4a13e4864a819b39b0f9f0bf5a2f953adcb1c86e` / `03fd4d5b04530f1bc2309c9b68b210dd299e4f53`.
Additive branch: `checkpoint/light-eft-native-budget-20261016`. CI skipped; independent review pending. No whole-paper acceptance is claimed.

## Prior review and scope

The user reports independent read-only acceptance of the original-ID seed-to-forest construction, fault erasure, actual-vertex doubling and congestion-two result, with its evidence reconciled. This records that supplied review, not fresh reviewer execution or CI. All 404 parent proof modules and the previous evidence manifest have been verified unchanged.

The new module NativeSeedBudget proves the weighted forest-budget interface and chooses its seed from the attained native minimum. Full aggregate validation remains open, including the 404-module parent and the resulting 405-module aggregate. The full weighted-multigraph bound and Theorem 34 remain open. Theorem 34 is unproved, not disproved. No other project source, website or optional runtime extension was modified.

## Derived weight budget

`forest_weight_le_two_seed` uses the existing `HostCounting.weighted_incidence` theorem over arbitrary original edge IDs E. Each forest B_i is a finite subset of H. Reordering the finite sums counts w(e) once for each forest containing e. The already-proved congestion bound is at most two, so nonnegativity gives

`sum_i totalWeight w B_i <= 2 * totalWeight w H`.

Weights are finite nonnegative real values represented by NNReal. No strict positivity, denominator division, endpoint-pair quotient, copied-edge weight substitution or desired final weighted inequality is assumed. Parallel IDs retain their own weights and memberships.

`SeedForestBudget` records a concrete family of q+1 original-ID forests, their containment in H, native forest properties, congestion, the weight bound and actual custom-walk witnesses for omitted-edge endpoints. `exists_seed_forest_budget` constructs this record from the accepted native seed-to-forest existence theorem and proves its weight field using the incidence calculation. It does not take a budgeted forest family as an unproved construction premise.

`exists_minimum_seed_budget` first uses the attained minimum connectivity-preserver theorem. It returns H and B with:

- H an actual q-fault connectivity preserver inside the original input IDs;
- weight(H) equal to minimumPreserverWeight, and no greater than any other feasible seed's weight;
- the constructed original-ID forest family and its actual omitted-edge walks;
- total forest weight at most twice that genuine minimum.

This includes empty inputs, q=0 and zero optimum. No positivity of the minimum is inferred. The proof chooses the same H whose optimality is established, rather than mixing weights from different seeds.

## Justified charging connections and remaining gap

`Walk.survives_disjoint` proves that a fault-free original-ID walk remains a surviving walk when its selected edge set is disjoint from the faults.

`SeedForestBudget.good_hosts` applies the existing arbitrary-ID `HostCounting.two_congestion_hosts`. For |F| <= f and the explicit coverage condition `2*f+h <= q+1`, it proves at least h unblocked forest members. Every member counted by this filter has an actual surviving custom walk for each omitted actual input edge's endpoints. Thus the counting is attached to genuine constructed forest connectivity, not an assumed host oracle.

`SeedForestBudget.real_weight_le` converts the proved NNReal budget into the real-valued congestion inequality used by `HostCounting.baseline_charging`. It supplies only that algebraic input.

The existing later `HostFamilyBound.spanning_host_family_bound` and its per-host candidate-weight theorem use simple graphs, Sym2 edge IDs, blocking data and additional host assumptions. They have not been applied to arbitrary native multigraph IDs. A native per-host candidate-weight bound, the relevant assignment/multiplicity construction, and any positive-denominator hypotheses needed for a ratio remain to be proved or justified. No such weighted estimate is assumed in the new unconditional seed-budget endpoint, and no final lightness ratio is claimed.

## Preflight and validation

Before any Lean invocation, evidence/preflight.json recorded the clean parent commit and remote, capacity, processes and repository-wide CI. in_progress, queued, waiting, pending and requested each had zero runs. No Lean/Lake/checker process was active. Capacity was approximately 23 GiB disk free, 16 GiB memory limit and four CPUs. All 90 reused project objects matched accepted hashes; reused-object-verification.json records this before invocation.

The only additional unchanged dependency compiled was HostCounting. No default Lake build, full aggregate build, parallel worker, new CI, dependency update, runtime shim or security-setting change was used.

Official Lean 4.34.0, Release, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, was used. All nine dependency revisions match the unchanged manifest; mathlib is 5ed2965256430c3649e86755f9576b54eca72435. Toolchain, dependency, source and all 92 loaded project object hashes are preserved.

NativeSeedBudget compiled with `-j1 -DautoImplicit=false -DwarningAsError=true` and zero diagnostics. Official `leanchecker -v LightEFTSpanners.NativeSeedBudget` passed for this individual module. The strict recursive audit passed: 798 actual-owner project roots, 18 covered declarations owned by the new module, 16240 recursively visited constants and 12 opaque bodies. It traverses types and bodies, including imported opaque bodies, and rejects unsafe/partial declarations and unexpected axioms. Only propext, Classical.choice and Quot.sound were found. This is the loaded 92-module closure, not full aggregate validation.

Five unique source-bound invocations are preserved: one dependency compile, one strict new-module compile, one individual replay, one strict audit and one version probe. All succeeded; there were no failed Lean attempts in this checkpoint. Two inherited warnings occurred in the unchanged HostCounting dependency: unused automatically included `[DecidableEq I]` in weighted_incidence (line 56), and the unreferenced `hadded` name in baseline_charging (line 80). These are unused-variable/section-variable lint warnings, not proof admissions or new-module warnings. Exactly two diagnostic headers are counted; hint text is not double-counted. Raw diagnostics remain intact and the old source was not edited to silence them.

All five invocations used the universal exclusive lock `/tmp/distance-sparsification-single-compiler.lock`. Reconciliation verifies UUID uniqueness, one lock inode, chronological nonoverlap, child reaping and source-snapshot hashes. Final compilation/replay hashes and the audit's directly submitted mathematical source match the frozen source. Full argv, options, environment, PIDs and UTC/monotonic times are in the receipts.

## Evidence and review handoff

After coordinating exclusive access, reproduce the bounded checks sequentially:

```
python3 checkpoints/light-eft-native-budget-20261016/run.py compile
python3 checkpoints/light-eft-native-budget-20261016/run.py replay
python3 checkpoints/light-eft-native-budget-20261016/run.py audit
```

The dependencies mode compiles the recorded HostCounting dependency when needed. The checks reuse the accepted imported object closure. `reconcile.py` invokes no Lean process; it checks source preservation, receipts, hashes and pins and regenerates derived evidence.

- evidence/source-object-hashes.json: immutable source, new source hash, 404 preserved proof hashes and 92 project object hashes.
- evidence/attempts/: authoritative source snapshots, raw logs and source-bound lock/PID/timing receipts.
- evidence/execution-reconciliation.json: sequencing and exact warning classification inputs.
- evidence/actual-owner-inventory.tsv and recursive-dependencies.tsv: complete raw audit.
- audit-export/manifest.json: 33 ordered row-aligned chunks and whole-file reconstruction hash; concatenate bytes in listed order without separators.
- evidence-sha256.json: packet-wide file sizes and SHA256 hashes.

Terminal checks show no compiler/checker process and a free universal lock. Publish this bounded additive source/evidence checkpoint with CI skipped, then pause for independent review. The remaining aggregate, native per-host weighted argument, full weighted bound and Theorem 34 obligations are unchanged.
