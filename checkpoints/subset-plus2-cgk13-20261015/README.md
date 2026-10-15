# Subset +2 development checkpoint: CGK13 contracts

Status: new supporting lemmas passed local strict compilation, six individual official kernel replays, and recursive axiom audit. **Not independently reviewed or accepted; no CI run for this checkpoint. UniformSubsetPlusTwo remains unproved.**

Work is confined to the same distance-sparsification paper. Accepted conditional source `d0f9ee2364bf4a5aaa7e0ca4da48216e42bbc63e` and all previous evidence remain preserved. Its independently reviewed CI run is [38818111905](https://github.com/gbodwin/paper-formalizations/actions/runs/38818111905), workflow trigger `6e02fb8a49b6a1d38a7bd195aa2bfbfd7069854c`; the [bounded acceptance record](../conditional-plus6-preserved-20261015/ci-gate/CI_ACCEPTANCE.md) is separate from this development.

## Source study

Primary source: Marek Cygan, Fabrizio Grandoni, Telikepalli Kavitha, *On Pairwise Spanners*, STACS 2013, DOI [10.4230/LIPIcs.STACS.2013.209](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2013.209). Studied the published [PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol020-stacs2013/LIPIcs.STACS.2013.209/LIPIcs.STACS.2013.209.pdf), Theorem 3 and Lemmas 5–8 (printed pp. 210, 212–214), through the browser. Shell PDF download returned 403; no local PDF identity/hash is claimed.

Theorem 3 gives subsetwise additive-2 sparsification. Lemma 5 supplies diameter-two clusters and retained edges. Lemma 6 counts clusters visited by missing shortest-path steps. Lemma 7 handles rejected paths. Lemma 8 charges purchased paths to source/cluster improvements. The implementation below replaces the real clustering exponent with a positive integer threshold; it does not attempt a complexity-theoretic formalization of polynomial running time.

## Correction in the formal route

Our formalization keeps global cluster distance and chosen-path distance separate. In the printed Lemma 7 argument, the buy rule uses path-restricted distances while subsequent displayed equalities use global minima. We do not assume those equalities.

For a concrete counterexample to that equality, take edges s–a, a–b, b–c, c–s, b–t, choose shortest path s–a–b–t, and cluster {b,c}. Its chosen-path prefix minimum from s is 2, but its global minimum is 1 via c; the cluster even has diameter 1. This example is explanatory mathematics, not an additional Lean-checked example in this checkpoint.

The proved routing uses only upper bounds by the restricted prefix/suffix minima. Both are bounded by lengths through one shared path occurrence, so diameter-two routing gives +2. Separately, shortestness and cluster diameter give restricted minimum ≤ global minimum +2, which is the charging argument's needed bridge. No conversion of infinity to a natural number is used without proving finiteness.

## Implemented modules and exact roles

All new modules are under `A Note on Distance-Preserving Graph Sparsification/SlackSparsification/`; none is added to the accepted aggregate.

| Module | Implemented contracts/results | Remaining premise |
| --- | --- | --- |
| SubsetPlusTwoCore | Extended cluster distance, attainment for nonempty clusters, monotonicity, unreachable cases, diameter routing, post-purchase bound, finite three-step obstruction | Supplied graph/cluster/prefix hypotheses |
| SubsetPlusTwoPaths | Actual shortest prefix/suffix distances; distinct path minima; global ≤ restricted ≤ global+2; rejection route; span-two and at-most-three occurrences | Supplied shortest walk and diameter bound |
| SubsetPlusTwoCharging | Unimproved-cluster counting; at most three strict improvements; total cost ≤6 times label count; graph-level charging including infinite global distance | Monotone graph sequence, strict improvements and post-purchase bound |
| SubsetPlusTwoIncidence | At most two missing source incidences and two target incidences per cluster; missing count ≤2 times visited-cluster count; full rejected-path route | Unique cluster ownership, retained intracluster edges, diameter bounds |
| SubsetPlusTwoParameters | Square-root integer rounding; budget 2nd+6sq≤8nd; implication IntegerSubsetConstruction G → UniformSubsetPlusTwo G 16 | **IntegerSubsetConstruction G is still unproved** |
| SubsetPlusTwoClustering | Precise ClusteringCertificate structure, star diameter, unique ownership; Lemma 6 from a certificate | **No certificate existence theorem yet** |

`ClusteringCertificate` and `IntegerSubsetConstruction` are definitions specifying obligations, not axioms or instances supplying them. Their appearance in checked statements must not be mistaken for a completed construction.

## Precise next construction obligations

The following are **proposed targets**, not declarations asserted or implemented by this checkpoint.

### Greedy clustering existence

For finite G and integer d>0, construct `cert : ClusteringCertificate G d` with:

- base ≤ G;
- pairwise disjoint clusters, each exactly d vertices;
- diameter ≤2 in base, all intracluster G edges retained;
- every omitted G edge has endpoints in different clusters;
- q*d≤n and base.edgeFinset.card≤2*n*d.

Implementation plan: recurse on the remaining unclustered finite vertex set U. When a vertex has at least d neighbors in U, choose exactly d of them, remove that cluster from U, and retain its induced edges and center edges. At termination retain every edge incident to U. Prove termination using d>0, ownership/disjointness, and the two separate finite edge budgets. Small/empty V and d>n must remain valid cases. The star-diameter and ownership lemmas are already available.

### Finite path-buying construction

Given such a certificate, finite S, d>0, and |S|≤d², construct H with:

```text
H ≤ G
H.edgeFinset.card ≤ 8 * Fintype.card V * d
∀ s ∈ S, ∀ t ∈ S, H.edist s t ≤ G.edist s t + 2
```

Enumerate distinct reachable ordered demands in S×S and choose actual shortest walks. Handle equal endpoints by edist_self and unreachable demands by the checked infinity lemma. For each walk define cost by the number of currently missing indexed steps (the existing missing_edges_card_le bounds actual added edges by this cost). Charge labels are actual source/cluster pairs; distinct endpoints prevent duplicate labels between the two endpoint sides.

Buy when cost≤2*value, retaining all path edges; otherwise apply the proved rejection contract. Establish by induction that H_i grows, stays between the base and G, and retains all previously satisfied pairs. In a bought step, prove clusterEDist after purchase ≤ the restricted path minimum, hence strict improvement and the checked post-purchase +2 window. The graph-level three-charge lemma then applies. Finally telescope added-edge counts and use total_purchase_cost_le_six with labels S×clusters. These sequence/capture/accounting invariants are **not yet implemented**.

### Uniform endpoint

The checked `uniform_of_integer_subset_construction` already handles S=∅ separately and otherwise chooses d=ceil(sqrt(|S|)), proving d>0, |S|≤d² and d≤2sqrt(|S|). A completed integer construction gives the conservative universal constant 16. This would discharge the exact pre-existing UniformSubsetPlusTwo interface; it would not by itself establish whole-paper completion.

## Validation and preservation

Toolchain: official Lean 4.34.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b; pinned dependencies unchanged. No other paper was edited or built. Twenty-eight previously validated supporting objects were copied into this checkpoint's isolated .lake output tree, avoiding needless rebuilding of accepted code; their hashes are recorded in supporting-object-hashes.json.

Every successful new module compile used `-j1 -DautoImplicit=false -DwarningAsError=true`; final diagnostics are empty. All failures and source snapshots are preserved as `evidence/attempt-NNN.{json,log,lean}`. Final successful attempts: Core 003; Paths 007; Charging 013; Incidence 016; Parameters 017; Clustering 018. Changes between attempts corrected elaboration, instances and linter issues; no linter or safety check was disabled.

Official `lake env leanchecker -v <exact leaf module>` passed for all six modules, one awaited process at a time. The new `verification/SubsetPlusTwoAudit.lean` inventoried 95 actual-owner new declarations (including generated structure declarations), recursively visited 13,667 constants and 13 opaque bodies, and found exactly propext, Classical.choice and Quot.sound. See the raw replay logs, actual-owner inventory, recursive-dependencies.tsv, and replay-Audit.log. No aggregate-prefix replay was used.

The branch guard excludes `checkpoint/subset-plus2-cgk13-20261015` from the general multi-paper job. Other workflows do not match this branch. Publication uses `[skip ci]`; any future CI requires coordination. No website change or certified-branch change. All raw evidence and source/object hashes are retained for independent review.
