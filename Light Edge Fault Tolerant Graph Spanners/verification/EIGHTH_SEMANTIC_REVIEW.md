# Eighth semantic component review: supplied spanning-packing assembly

**PASS for the three frozen sources and their explicitly conditional scope. No semantic blocker found.** This is a bounded component review, not a fresh skeptical whole-paper final audit.

Reviewed 10 October 2026 (UTC). Proof sources were read only. No compiler, axiom auditor, kernel checker, or child agent was run by this reviewer. The only new file produced is this review record.

## Exact sources and separate verification evidence

All three SHA-256 hashes were independently recomputed from the actual files under `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/` and match `eighth-source-hashes.json`:

- `HostFamilyBound.lean`: `ad0abd9d2a24c13924375da6faa2e5759df7189ac6906b49bab02f5226ef3812`
- `SpanningHostAssignments.lean`: `e4b7578db11870ef7bc0ade317415f73bd3c34f7ecfc1ec4306d73f673628d3b`
- `SeededSpanningPacking.lean`: `aad87e7b6889dcebe765e3219ba4e08d99f86f362045de9d323e56086bf47e81`

Inspected `verification/eighth-build.log`, `verification/eighth-replays.log`, and their shell runners. The build log records compilation of the three additions, the 377-declaration allowed-axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`, the successful generated-import check, and aggregate gate completion. The coordinator reports the full 39-module/root/index gate passed. The replay log names all three new modules and ends with `EIGHTH_REPLAYS_PASSED`; the coordinator reports these are exact-source official kernel replays. These are separate gate evidence, not verification rerun by this reviewer. The review brief's earlier “queued” replay wording is superseded by this evidence.

Read the actual relevant contracts and proofs in `HostGraphSampling`, `HostCounting`, `Blocking`, `SeededGreedy`, `ConnectivityOptimum`, and `Basic`, plus the imported total-weight, minimum-tree, and tree-weight-positivity definitions. Consulted the initial, second, and fifth component reviews. The actual `HostGraphSampling` hash remains `0a50479e89429b47d9c8039277d4c992daec9038cf4dcbb75cbd0c781394afcb`, matching its fifth-review frozen source.

## 1. HostFamilyBound: actual incidence and seed baseline

`spanning_host_family_bound` (lines 15–73) receives actual finite indexed graphs and actual candidate edge sets. Every `T i` is a genuine `SimpleGraph V` tree, hence spans the same entire finite vertex type; `T i ≤ Q ≤ G`. Candidates belong to actual `G` edges, are outside `Q`, and avoid their host tree's blockers. Coverage and congestion refer to the real `hosts` definition, an index finset filtered by membership in an assigned edge finset. Repeated tree contents at different indices are counted separately, as they must be.

With `E = G.edgeFinset \\ Q.edgeFinset`, the proof establishes `U i ⊆ E`, applies exact weighted incidence, and obtains `h * weight(E) ≤ sum_i weight(U i)` from actual coverage and positive edge weights. It invokes the already reviewed `host_candidate_weight_bound` for each tree, rather than assuming a per-host weight conclusion. That dependency constructs the sampled/pruned graph and a genuine minimum spanning tree and gives `weight(U i) ≤ 4fL * weight(T i)`, where

`L = 8 + 2048/eps * n^(1/k)` and `n = Fintype.card V`.

A second actual incidence identity and the stated congestion-two premise give `sum_i weight(T i) ≤ 2 * weight(Q)`. Only then is the algebraic `baseline_charging` lemma applied. Finally, inclusion `Q ≤ G` proves the exact decomposition `weight(G) = weight(Q) + weight(E)`. The exported bound is precisely `weight(G)/weight(Q) ≤ 1 + 8fL/h`. The seed's additive baseline 1 is retained, not absorbed or dropped. Positive seed weight, positive `h`, positive `f,k,eps`, positive graph-edge weights, and `n ≥ 2` remain explicit assumptions at this layer.

## 2. SpanningHostAssignments: constructed coverage and outside-seed blockers

`unblockedAssignments` (lines 10–12) is literally the finite set of non-seed `G` edges filtered by `Disjoint (B e) (T i).edgeFinset`. It does not encode any weight conclusion.

The supplied congestion premise applies only to actual `Q` edges. Lines 30–38 correctly extend it to every unordered pair: for `e ∉ Q.edgeFinset`, any tree incidence would contradict `T i ≤ Q`, so its host finset is empty and its cardinality is zero. Thus blockers outside `Q` receive zero incidence by proof; no extra unjustified congestion assumption is introduced for them.

For every candidate edge, `BlockingData.capped` bounds its actual blocker finset by `f`. `two_congestion_hosts` uses a finite union bound over the incidences of these blockers. At most `2f` supplied indices are blocked. The explicit premise `2f+h ≤ indices.card` therefore gives at least `h` unblocked hosts. Lines 50–55 identify those hosts with the actual constructed assignment hosts, using commutativity of disjointness. Candidate membership, exclusion from `Q`, and blocker avoidance are also projected directly from the filter. Coverage and avoidance are derived here, not assumed as additional properties of an abstract assignment oracle.

## 3. SeededSpanningPacking: actual algorithm, optimum, and positive ratio

`seed_le_output` (lines 11–14) transfers the proved recursive seed-edge inclusion to actual graphs. The underlying `output` is exactly `edgeGraph (greedyEdges Q.edgeFinset ... (input G Q w))`. The duplicate-free input filters out seed edges from a descending-weight list; tail-first recursion processes the remaining edges in nondecreasing order, inserting precisely when the actual fault-coverage test fails. This is not a graph chosen to satisfy the final result.

`output_has_blocking` supplies a map for that same actual output. Its underlying induction takes bounded old-edge fault witnesses from rejected tests and assigns them to inserted edges. Its contract guarantees actual first and second graph edges, first edges outside the seed, no self-blocking, a cap of `f`, and the cycle-blocking property. It assumes neither the target lightness inequality nor an external blocking oracle.

`hQ : IsMinimumFTPreserver G Q w q` means genuine all-fault connectivity preservation and minimum actual total edge weight among every eligible `q`-fault preserver. The imported finite-minimum theorem proves attainment independently. This wrapper receives such a `Q`; it does not construct a packing for it. Although its proof only needs the subgraph part of `hQ`, the full minimum property remains in the theorem's premises, so its denominator really is an optimum for the stated budget `q`.

Denominator positivity is proved, not passed in: the index-count and `h>0` premises supply an actual index; that tree has at least one edge because it spans `n≥2` vertices; strict positivity of input-edge weights makes its total weight positive; and `T i ≤ Q` plus nonnegative weights gives `weight(Q) ≥ weight(T i) > 0`. This excludes an accidental appeal to Lean's zero-denominator convention. Global nonnegativity `∀ e, 0≤w e` and strict positivity on actual input edges remain explicit, separate assumptions.

The stretch `(1+eps)*(2*k-1)` is proved at least 1 from `k>0` and `eps>0`. `output_isEFTSpanner` then proves the spanner property. Its graph inclusion transfers positive input-edge weights to the output before applying `spanning_packing_lightness`. Both conjuncts of the final theorem use exactly the same output expression, weight function, fault budget, and stretch. `competitiveLightness` unfolds to its actual total weight divided by `weight(Q)`.

## Scope and remaining obligations

There is no final-result assumption or hidden unconditional upper theorem in these sources. The theorem comments explicitly disclose conditionality; the inspected README still labels the main upper bounds open.

The supplied family is a strong hypothesis: all trees span the common vertex type, lie in the genuine minimum seed, number at least `2f+h`, and have actual seed-edge congestion at most two. The theorem states no relation deriving that family from `q`, `f`, or a connectivity premise. In particular it proves neither its existence nor the packing needed in the general paper setting. General subtree vertex-set transport, forest/Eulerian packing existence, optimized upper-bound assembly, degenerate parameter cases outside the displayed hypotheses, and polynomial runtime remain separate obligations. `BlockerTransport` and `HostWeightTransport` drafts were outside this review and were not inspected or certified.

**Conclusion:** the batch validly closes the conditional common-vertex spanning-host assembly, including constructed assignments and its join to the actual seeded algorithm. It does not close the unrestricted paper upper theorem or the whole-paper audit.
