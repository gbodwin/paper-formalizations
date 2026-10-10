# Ninth component semantic review: genuine induced-host transport

**Verdict: PASS.** No semantic/source blockers found in the three frozen production modules. This is a bounded component review, not the final whole-paper audit.

Reviewed on 2026-10-10 UTC. The review read actual source, checked the frozen SHA-256 values, and inspected the relevant upstream definitions and theorem contracts. No compiler was run, no proof source was edited, no child was created, and no external write was made.

## Frozen source identity and supplied verification

Paths below are relative to `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/`.

| File | Verified SHA-256 |
| --- | --- |
| `BlockerTransport.lean` | `17b104d28fa74990470003facb05e8576ecf0f74d4dfaaebace3704bc4744e77` |
| `HostWeightTransport.lean` | `b9d7609e9d94e4885b73641b20bbca6fad0ca8e414f9282a7a709feecb8165a8` |
| `InducedHostSampling.lean` | `e021f0042e9839ec0de00166c62f78187f643ec3f6b24f9811a9a636c8853b3d` |

Each matches `review/ninth-source-hashes.json`. The supplied `verification/ninth-build.log` records all three builds, the allowed-axiom audit of 398 declarations (only `propext`, `Classical.choice`, and `Quot.sound`), and `NINTH_AGGREGATE_GATE_PASSED`. The owner identifies this as the complete 42-module root/index gate. `verification/ninth-replays.log` names each of the three exact-source replays and records `NINTH_REPLAYS_PASSED`. These are inspected owner-run verification records, not fresh compiler or kernel runs by this reviewer.

## Findings

### 1. Actual blocker restriction and cycle transport

`BlockerTransport.lean:9–24` defines `pullEdges j E` as the actual inverse image of the finite unordered-edge set under `j.sym2Map`. The map is an embedding `j : V ↪ W`, not a potentially identifying vertex map. The cardinality bound maps the inverse image injectively into `E`; consequently every local blocker set has cardinality at most the original cap `f`.

`Blocking.lean:10–17` defines the inspected upstream `BlockingData` contract: blocker cap, actual graph membership of both edges, exclusion of seed first edges, no self-blocking, and an actual blocking pair on each qualifying actual graph cycle. `BlockingData.comap` (`BlockerTransport.lean:36–66`) derives every local field from that original structure. In particular:

- `mem_comap_edgeSet` supplies exact local/global edge membership correspondence.
- First-edge, second-edge, non-seed, and no-self properties are pulled back from the supplied original blockers.
- A local closed walk maps through `SimpleGraph.Hom.comap j G` to the original graph; `hp.map j.injective` proves that it is still a genuine cycle.
- Seed exclusion and the exact `(t+1) * w d` weight threshold survive transport. `LightSpanners.CycleProjection.walkWeight_map` is an equality of the actual sums over walk edges, not an inequality or an abstract weight oracle.
- The original `hB.blocks` is invoked on that mapped cycle. Both returned edges lie on its actual edge list, so `Walk.edges_map` supplies local preimages of both. Their original blocking relation then gives the local inverse-image relation.

No local final blocking theorem, replacement blocker oracle, additional blocker cap, or assumed cycle projection conclusion is introduced.

### 2. Exact unordered-edge and weight transport

`HostWeightTransport.lean:11–36` proves the mapped edge-finset equality for independently supplied finite enumerations of the local and mapped edge sets. It passes through equality of the underlying sets and `G.edgeSet_map j`, so the argument does not depend on a particular `Fintype` enumeration.

The inspected definition `LightSpanners.MinimumTree.lean:23–24` is the finite sum of `w` over actual unordered graph edges. Accordingly, `totalWeight_map_embedding` rewrites that sum with the exact edge-finset equality and `Finset.sum_map`. Each unordered edge is counted once. There is no orientation factor, collision multiplicity, normalization, or positivity premise concealed in this equality.

`pullEdges_edgeFinset` (`:40–43`) gives exactly the edge set of the comapped seed graph. `disjoint_pullEdges_host` (`:47–60`) proves equivalence between local blocker avoidance and avoidance of the actual mapped host tree; blockers outside the host's image do not create fictitious local obstructions. `mapped_candidate_weight` (`:64–66`) likewise transports the candidate sum exactly through an injective finset map.

### 3. Genuine finite local host domains and upstream sampling contract

`induced_host_candidate_weight_bound` (`InducedHostSampling.lean:12–36`) permits independent finite types `V` and `W`, an embedding `j : V ↪ W`, and a supplied tree on `V`. Its graph premise is `T.map j ≤ Q ≤ G`. This supports actual subtree vertex sets, including proper subsets of the original vertex domain. It does not require `T.map j` to span or connect all of `W`, nor does it require all of `G` or `Q` to be connected. The ambient local graph is the induced/comapped graph `G.comap j`; the supplied tree itself need not be the entire induced graph.

Every candidate is an actual original graph edge with endpoints in the host image, is outside the original seed `Q.edgeFinset`, and avoids its original blockers on the actual mapped tree. Local host containment, local seed membership, local candidate membership/non-seed status, local blocker avoidance, and local edge-weight positivity are each derived explicitly before applying `host_candidate_weight_bound`.

The inspected upstream contract (`HostGraphSampling.lean:80–105`) requires an actual supplied tree, genuine `BlockingData`, actual non-seed candidates, actual blocker avoidance, positive graph-edge weights, positive natural `f` and `k`, positive `eps`, and local order at least two. It concludes the same explicit per-host bound with coefficient

`4 * f * (8 + 2048 / eps * |V|^(1/k))`.

Its preceding `exists_heavy_girth_host` theorem constructs the sampled/pruned graph and a minimum spanning tree; a final candidate-weight inequality or high-girth graph is not supplied as a premise. The threshold contract is the corrected actual threshold `(1+eps)*(2*k-1)+1`, as seen in `StretchParameters.lean:19–40`, rather than the larger printed threshold. This review checked these relevant contracts and the local wrapper's use of them; it did not repeat their full upstream audits.

### 4. Global order, positivity, and degenerate cases

`induced_host_bound_in_global_order` (`InducedHostSampling.lean:40–82`) has no local or global minimum-order premise.

- It derives nonnegativity of the actual mapped host weight directly from `T.map j ≤ Q ≤ G` and positivity on actual global edges (`:51–57`). No positivity is imposed on nonedges.
- If the candidate set is nonempty, an actual global edge supplies two distinct local endpoints. Looplessness excludes equal endpoints, yielding `2 ≤ |V|` (`:58–67`); thus the first wrapper's size premise is justified rather than silently assumed.
- `|V| ≤ |W|` follows from the actual embedding's injectivity (`:70–71`). Real cardinalities are nonnegative, and the exponent `(k:ℝ)⁻¹` is nonnegative. The application of `Real.rpow_le_rpow` therefore has the required direction and sign premises (`:72–73`). Positive `eps`, positive natural `f`, and nonnegative host weight justify the subsequent multiplications.
- If the candidate set is empty, the left side is exactly zero and the right side is nonnegative (`:80–82`). No division by the host weight occurs here. A singleton local host cannot have a nonempty set satisfying the actual-edge candidate premise, so it is covered by this empty-candidate case. In particular, a zero-weight singleton tree is not excluded. The tree premise retains its ordinary mathematical meaning; the theorem does not assert the existence of a tree on an empty vertex type.

## Scope and limitations

This PASS establishes semantic agreement of the frozen transport components with their stated per-host contracts. The results remain conditional on the supplied actual blocking data, embedding, host tree, seed containment, and candidate/blocker conditions. They do not construct an Eulerian forest packing, produce a dependent family of hosts, prove incidence/assignment coverage across that family, or assemble a global main upper theorem. Those existence and assembly obligations remain open. No main theorem or whole-paper completion claim follows from this component review.
