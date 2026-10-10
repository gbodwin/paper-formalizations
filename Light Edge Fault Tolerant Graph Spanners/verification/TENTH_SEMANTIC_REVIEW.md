# Tenth component semantic review: subtree-family assembly and seeded output

**Verdict: PASS.** No semantic or frozen-source blockers found in the three reviewed production modules. This is a bounded component review, not the final whole-paper audit.

Reviewed on 2026-10-10 UTC. The review inspected the actual production source and relevant upstream definitions/contracts. No compiler or kernel replay was run by this reviewer, no proof source was edited, no child was created, and nothing was published externally. Only this requested review report was written. ForestComponents, ForestComponentPacking, and RoundedCompetition were outside scope.

## Frozen source identity and verification evidence

The following SHA-256 values were recomputed from the production files under `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/` and match `review/tenth-source-hashes.json`:

| Module | SHA-256 |
| --- | --- |
| SubtreeHostFamily | `965734dd9cd67d8e28eea0b6a932a209513fbeedd2f23fcba9d7baf2bb36ab83` |
| SubtreeAssignments | `d72d4decda94a16ee734f2e43b10020ca9c92e84fcda399df6ad601b4451ecb1` |
| SeededSubtreePacking | `6e9e954b31ad41df975d725eaa9d0dfcd207ad8aca1bc77a8922df017cc676b3` |

The inspected `verification/tenth-build.log` records the three builds, 403 audited declarations using only `propext`, `Classical.choice`, and `Quot.sound`, and `TENTH_AGGREGATE_GATE_PASSED`. The owner identifies this as the complete 45-module/root/index gate. The inspected `verification/tenth-replays.log` names all three exact-source replay targets and ends with `TENTH_REPLAYS_PASSED`. These are supplied verification records, not new runs performed by this reviewer.

## 1. Genuine heterogeneous host family and exact transport

All three modules quantify a dependent family `A : I → Type*`, with finite and decidable-equality instances for every `A i`, and embeddings `j i : A i ↪ V`. The finite collection is `indices : Finset I`; no unnecessary global finiteness assumption on `I` is imposed. Each supplied `T i` is an actual tree on its own local domain, and only its mapped graph must lie in `Q`. The local domains may have different cardinalities and need not span `V`.

`SubtreeHostFamily.lean:27–40` requires genuine local candidate finsets. Their images must be actual edges of `G`, outside `Q`, with their original blocker sets disjoint from the actual mapped tree. These are ordinary graph/set premises, not assumed final weight bounds.

The inspected upstream `HostWeightTransport.lean:11–36,64–66` proves exact mapped edge-finset and weight equalities through `j.sym2Map` and `Finset.sum_map`. Injective vertex maps induce injective unordered-edge maps, so there is neither an orientation factor nor a collision multiplicity. The local theorem used at `SubtreeHostFamily.lean:63–64` is `induced_host_bound_in_global_order`; its actual contract and implementation were inspected in `InducedHostSampling.lean:40–82`. It uses the comapped graph, original transported weights, seed, and blockers. Nonempty candidates establish at least two local vertices; empty candidate sets are handled separately. Injectivity bounds the local order by the global order. Consequently this family wrapper introduces no hidden minimum host or global graph size.

The upstream `HostGraphSampling.lean:80–105` requires the actual supplied tree/candidates and `BlockingData`, then derives the per-host coefficient `4*f*L`, where `L = 8 + 2048/eps * |V|^(1/k)` after the local-to-global order comparison. Its sampled/pruned graph and minimum tree are constructed by the preceding theorem, rather than supplied as the desired charging conclusion. This review checked those relevant contracts and their composition; it did not repeat the full prior upstream audits.

## 2. Actual finite incidence and the seed baseline

`SubtreeHostFamily.lean:44–57` sets the charged edges to precisely `E = G.edgeFinset \\ Q.edgeFinset`. Membership in this actual difference is derived for every mapped candidate. `HostCounting.weighted_incidence` rewrites the sum over hosts as the sum over edges with their actual host multiplicities. The premise of at least `h` appearances therefore gives `h * weight(E)` bounded by the summed candidate weights, using positivity on the same actual graph edges.

The host-tree sum receives the same incidence treatment at `SubtreeHostFamily.lean:65–80`. The private `weight_eq_edge_sum` lemma (`:12–22`) explicitly reconciles the finite enumeration used by `totalWeight` with the one used in the displayed edge sum. Its use at `:69–75` prevents an implicit enumeration mismatch. Congestion at most two and `T_i.map j_i ≤ Q ≤ G` then give the actual inequality `sum_i weight(T_i.map j_i) ≤ 2 * weight(Q)`.

Finally `:81–90` splits the actual graph weight as `weight(Q) + weight(E)` and applies the inspected `HostCounting.baseline_charging` contract. Thus the conclusion is `1 + 8*f*L/h`, with the seed's baseline **1** retained. No abstract host-weight oracle or already-proved global lightness inequality is an input. The positive denominator and positive `h` needed here are explicit premises of this intermediate theorem.

## 3. Actual joint-endpoint assignments and restricted survivor counts

`SubtreeAssignments.lean:11–15` defines the candidates rather than postulating them: pull back the actual non-seed edges, then filter by avoidance of the original blocker set on the mapped host tree. The inspected `BlockerTransport.mem_pullEdges` says membership is exactly membership of the mapped edge in the original finite set.

For a fixed actual non-seed edge `e`, `goodDomain` (`:57`) consists only of indices for which there exists an unordered local edge `d` with `j_i.sym2Map d = e`. This requires both actual endpoints to belong to the same host's vertex image. It is not merely a nonempty intersection with that image. Because `e` is an actual simple-graph edge, its endpoints are distinct, and injectivity rules out a diagonal local preimage.

The survivor count is applied to this restricted eligible index set, with the supplied lower bound `2*f+h`; it is not applied indiscriminately to every tree. At `:58–64`, restricted congestion is proved by inclusion in the full host set.

Blocker edges need not belong to `Q`. The auxiliary `hcongAll` (`:36–46`) handles this correctly: an edge outside `Q` occurs in no mapped host tree because every such tree is contained in `Q`. Thus its host set is empty. Together with the original congestion premise for edges inside `Q`, this proves the congestion bound for every blocker, without adding an unsupported `B e ⊆ Q` assumption.

`HostCounting.two_congestion_hosts` uses the actual blocker cap `(B e).card ≤ f` and congestion two to leave at least `h` avoiding eligible trees. The bidirectional equality at `SubtreeAssignments.lean:67–88` identifies those survivors exactly with the hosts containing `e` in the mapped, filtered candidate assignment. The reverse direction uses the actual non-seed membership of `e` to put its local preimage into `pullEdges`. This closes the assignment/coverage link rather than assuming it.

## 4. Joined optimum-seeded recursive output

`SeededSubtreePacking.lean:14–27` assumes `IsMinimumFTPreserver G Q w q`. The inspected definition in `ConnectivityOptimum.lean:11–13` means actual fault-connectivity preservation plus minimum total weight among all such preservers; it is not a renamed arbitrary seed.

The theorem uses the actual `output` from `SeededGreedy.lean:107–114`: a recursive edge insertion procedure initialized with `Q.edgeFinset`, processing the weight-ordered input edges outside `Q`. `output_isEFTSpanner` supplies the actual fault-tolerant spanner property and `output ≤ G`. The inspected `seed_le_output` supplies `Q ≤ output`. The source stretch is consistently `(1+eps)*(2*k-1)`; `k > 0` and `eps > 0` justify the required stretch inequalities.

In the nonzero-denominator branch, `output_has_blocking` supplies a blocker map for that exact output, same seed edge set, same weights, stretch, and fault budget. The call to `subtree_packing_lightness` therefore concerns that same output graph. At `SeededSubtreePacking.lean:45–49`, coverage assumed for input non-seed edges is restricted through `output ≤ G`, and input-edge positivity is likewise restricted to output edges. There is no substitution of an unrelated graph, weight function, sample, or blocker oracle.

The conjunction consequently proves the actual output's EFT property and the conditional competitive-lightness bound `1 + 8*f*L/h` under the supplied structural packing.

## 5. Denominator convention and remaining boundary

`competitiveLightness` is actual real division of graph weight by seed weight (`ConnectivityOptimum.lean:42–43`). The zero branch at `SeededSubtreePacking.lean:35–37` uses Lean's total convention `x / 0 = 0`. This proves the displayed formal ratio inequality in that branch; it does **not** establish positive seed weight or give a nontrivial positive-denominator interpretation of lightness.

Only in the nonzero branch does global nonnegativity of `w` imply nonnegative seed weight and hence strict positivity (`:38–41`). Global nonnegativity and strict positivity on actual input edges are explicit assumptions, as are positive natural `f`, `k`, `h` and positive `eps`. No graph nontriviality or order lower bound is hidden.

The minimum-seed hypothesis supplies an authentic optimum seed, but this assembly proof only uses its subgraph consequence. No relation between the seed fault budget `q` and the packing parameters `f,h` is derived here: `q` remains independently quantified. Existence of the required heterogeneous tree family, its endpoint coverage, congestion, and the argument connecting those structural properties to the desired seed fault budget remain open obligations. No unrestricted main upper theorem or whole-paper completion follows from this PASS.
