# Nineteenth bounded semantic/source review

Date: 2026-10-11 UTC. Frozen six-file, 97-module checkpoint.

Verdict: **COMPONENT PASS. No semantic blocker found in the six frozen modules.** The packet constructs a genuine original-edge lower-level tree exchange and its within-level replacement route, and proves the stated conditional all-stage preservation helper. It does not assemble the swapped coloring or finish the lexicographic contradiction or packing theorem.

## Scope and identity

I read all 355 lines of the six production sources, relevant native bridge, forest-selection/cardinality, minimum-level, edge-level and exchange-connectivity dependencies, the underlying Mathlib graph/restriction/deletion/bridge/simple-adjacency definitions, and the pinned Kaiser source, especially pages 3–4. No compiler or checker was invoked. No proofs, repository state, GitHub content or Site were edited. Only this report was written. `NativeColorExchange` and `NativeColoredExchange` drafts are outside this review.

Independently verified identities:

- Repository: `gbodwin/paper-formalizations`; branch: `light-eft-spanners-checkpoints`.
- Published proof commit: `52cd0ab93531cbbbe5741842ab70b55aebe36c06`.
- Tree: `13a6648ec36ba5eafeaf416fccdd3c54de0f7781`.
- Prior reviewed91 parent: `89bda02eff2eb0737f69c4fff30a95063b42c37f`.

GitHub's commit and branch APIs confirmed this head, tree and parent at approximately 00:57 UTC. I also rehashed the local raw commit object to the same commit ID. The review manifest, production manifest, current production source bytes and exact committed bytes agree. All six files were independently fetched from GitHub at the pinned commit; their returned contents equal local bytes, their recomputed SHA-256 hashes match the freeze, and their recomputed Git blob IDs match the API's blob IDs.

| Module | SHA-256 |
|---|---|
| NativeTreeCertification | 038ffd050fb6138afc702bbc649ecad5e649119f7bc40426df5620b82f944be1 |
| NativeDeleteNonbridge | fbafd1c76490901cee95e3fd1f539d8349ea49258e2ecb976e4b5e86e5d24f9e |
| NativeTreeExchange | c1fe6b4517d202d50587fc8bb93f777050b7d34a464e8c08488131187b81c201 |
| NativeEdgeLevelTransport | 7bb49555bf284d18e2c019a1a7bd5c2c399eb8e10d96e81a5c7b37177cb54ea0 |
| NativeLowerExchange | 81f435c6d948627d619d7df871301210f0919fafc4f6d2358ea3ca185f907802 |
| NativeLevelExchangePreservation | 9b46b3ea88b0ba420cd9dec24c751c13b171d90c740eb18e63c1a59da4b9637d |

All 91 prior production module files are byte-identical to the parent. The independent remote comparison is one commit ahead and shows exactly six added Lean modules, six added root imports, and accompanying documentation/evidence changes, with no prior module modification. Earlier reviews are inherited by this equality, not repeated in full. There are exactly 97 production module files and 97 distinct root imports with equal sets and no duplicates. The human statement-map union also covers exactly those 97 modules, including the previously omitted `HostCounting`. The working tree was clean during inspection.

## Validation evidence and limits

The four workspace/production/committed nineteenth gate logs agree byte-for-byte. I read the strict-build and replay scripts and their wrappers. The six production builds use `-DwarningAsError=true`; the wrapper supplies `-DautoImplicit=false`. The second build group compiles the aggregate root, performs the project-declaration transitive-axiom audit and runs the module-index check. Its log records 743 declarations allowing only `propext`, `Classical.choice` and `Quot.sound`, index success, and `NINETEENTH_AGGREGATE_GATE_PASSED`.

The official `leanchecker` wrapper is invoked by both replay groups, and the logs contain individual successful replay markers for all six modules. This corroborates the owner's reported gate/replay completion. These are inspected records, not fresh runs by this reviewer; the first build-group log alone does not encode its process exit status. Prior91 objects were reused locally. This review makes no claim of a full clean97 local rebuild or successful exact97 remote CI, which remain distinct checks.

No `sorry`, `admit`, custom `axiom`, unsafe declaration or implementation override occurs in the six frozen files. Their conclusions are not smuggled in through a cycle, exchange-edge or replacement-route premise in the joined construction.

## Semantic findings

### 1. Native trees and exact original-edge counts

Mathlib's `Graph V E` retains edge identities and a separate actual vertex set. Restriction intersects with the original edge set and keeps the vertex set unchanged; deletion removes the specified identities before conversion to simple adjacency. A native bridge is a singleton original-edge cut. The reviewed bridge/deletion equivalence therefore handles parallel survivors and loop endpoint reflexivity correctly.

`native_all_bridges_of_connected_card` assumes finite actual vertices, finite actual edges, genuine connectedness and the exact equation |E| + 1 = |V|. It first invokes the prior construction of a native spanning tree, then uses finite subset/cardinality equality to show that the selected edge set is all of G's original edges. It does not infer native acyclicity merely from acyclicity of simplified adjacency. Its resulting all-edges-bridge property excludes loops and parallel cycles as a proved consequence.

The finiteness hypotheses are important because `Nat.card` on an infinite type is not a finite count. They are present where this characterization needs them. Connectedness supplies nonemptiness, and every vertex count is over `G.vertexSet`, not the ambient type V. The supporting spanning-forest construction chooses one actual identity per selected unordered adjacency, proves its simplicity and projection equality, and thus yields an actual original-edge forest rather than only a simplified graph.

### 2. Nonbridge deletion and an external witness

`native_reachable_delete_nonbridge` replaces each adjacency step of an old walk by either the same surviving identity or an endpoint route avoiding the deleted identity, using the native bridge/deletion equivalence. It preserves arbitrary actual reachability; the connectedness wrapper preserves the same full actual vertex domain. There is no finite-domain assumption needed for this step.

`exists_external_nonbridge_of_no_block_route` uses the previously constructed route in the nonbridge core after deleting the chosen edge. If every nonbridge were internal to the partition, all steps of this actual route would lie in the block graph, contradicting the explicit no-block-route premise. Its witness is an actual original nonbridge, not a supplied external edge or cycle. `[Fintype E]` explicitly supports the inherited finite-cut argument. The route construction works with a surviving parallel identity, rather than deleting its entire unordered pair.

### 3. Actual exchanged native tree

`native_tree_exchange` explicitly assumes a finite set F of genuine original edges forming a connected native forest, a genuine absent inserted edge e, an old edge d in F, and nonbridge status of d after insertion. The different identities follow from d in F and e not in F. This local wrapper does not purport to derive its nonbridge premise.

The inserted graph is connected by retaining the old tree's walks; deleting d preserves connectedness. The proof establishes exact edge-set equality with `insert e F`, deletes precisely d, and computes the resulting cardinality as `F.card`. The old tree count then gives |E(new)| + 1 = |V|, and the preceding finite characterization proves every new native edge is a bridge. This is a genuine spanning tree on the same vertices, including original multiplicities, rather than an assumed acyclic swap.

### 4. Exact finite-level transport

`edgeInside_restrict_iff` explicitly requires retention of the queried identity. Since restriction preserves the actual vertex domain and endpoint relation, it proves equality of the entire internal-stage sets and hence equality of levels. No equality is claimed for a deleted identity.

`not_inside_terminal_of_level_lt` shows that a level below N cannot be an edge internal at N. `edgeLevel_truncate` uses the explicitly antitone R and m <= N: an edge crossing stage m cannot be internal at any later stage. Consequently the internal-stage sets through N and through m coincide exactly. The antitone direction is correct.

The finite bound N remains a terminal sentinel, not a literal infinity. The lower-exchange use has top initiality and an actual retained edge, so the default zero for an empty stage set is not misused. The global wrapper proves equality with the original G's level at N for the selected exchange identity, rather than silently substituting a restriction-local or truncated level.

### 5. The lower exchange is constructed without circular premises

`exists_lower_tree_exchange` takes a genuine native tree F; a genuine absent e; an antitone, top-initial partition sequence; internality of e at m; and actual failure of a tree route between its endpoints inside the m-block. The tree/inserted-edge/block-separation conditions remain explicit local inputs corresponding to the source's earlier-color countercase. They are not a supplied cycle, exchange edge or replacement route.

The old connected tree supplies a route after deleting the newly inserted identity, proving e is a nonbridge in H = F + e. Deleting that new identity cannot create a missing tree-block route. The no-block-route theorem therefore constructs an external nonbridge. The inherited minimum-level theorem now selects an actual H-nonbridge d of level below m and constructs its route avoiding d inside its own level block.

The inserted e is internal at m and therefore cannot equal the selected lower-level d. Thus d is in F. The tree-exchange wrapper certifies H - d and its exact edge count. Every step producing d, its nonbridge status and its replacement route occurs inside the proof. The global wrapper transports d's local level to exactly `edgeLevel G R N d` and returns the same native exchanged tree and route.

The published output does not expose the inherited minimization certificate or next-stage boundary, although they are available in the underlying minimum-level result; it promises the strict lower-level witness and within-level route actually stated. Nor does it package an explicit fundamental-cycle object or uniqueness theorem. Actual reachability suffices for this exchange and the later connectivity obligation. Impossible loop or m = 0 countercases are ruled out by the existing internality/top/connectedness/separation premises, without an unstated simplicity assumption.

### 6. Conditional all-stage preservation has the right scope

`native_level_exchange_preserves_all_stages` is deliberately generic. It assumes all old identities except the removed e survive in F', a replacement route in F' inside stage m, and that e crosses stage m + 1. For i <= m, antitonicity puts the route inside stage i. For i > m, e cannot appear in a stage-i block walk, so all its steps survive literally. The proof preserves each supplied old within-stage reachability statement for every natural i, including stages beyond a chosen finite sentinel.

The replacement route and next-stage separation are genuine premises here. There is no claim that this helper itself constructs a swap, proves new-color tree status, or proves equality of old and newly recomputed refinement sequences. It refers throughout to the supplied original R. This distinction is essential when using the helper in the still-open colored-decomposition assembly.

## Correspondence with Kaiser and remaining work

Primary source: [Tomáš Kaiser, A short proof of the tree-packing theorem, arXiv:0911.2809v3](https://arxiv.org/pdf/0911.2809v3). The pinned PDF SHA-256 is `4bef0841bbfe41cc93c2edfa33ec6649c56f7810e6e5dc932e053dec1a85808b`; the extracted-text SHA-256 is `58342327af7f9d3cd5586549b12eb2ea53ab7018fc2a557dc6fc3859ffcde506`, both independently recomputed. The article expressly permits loops and parallel edges.

On page 3 the earlier-color tree and the endpoints' separation inside P force its inserted-edge cycle to leave P; a lowest-level old edge gives a strictly lower level. Page 4 uses the cycle-minus-edge route within Q to preserve relevant connectivity. The packet supplies these local consequences with native nonbridge-core routes and exact original identities. It does not need to assume or store the cycle object to establish them. Its all-stage helper supplies the partition-block connectivity implication used in Claim 1, not a complete formalization of Claim 1 for arbitrary subsets X or Claim 2 for the new refinement process.

Still open: concrete two-color swap and coloring coverage/disjointness, all affected color-class transformations, connection to the selected earlier color and the last-color route, lexicographically maximal decomposition choice, preservation/comparison of the new refinement stages and least colors, and the strict-improvement contradiction. Inductive decomposition assembly, general tree/Steiner-forest packing, Mader splitting, Steiner expansion, weighted/fractional scope, runtime and the Light EFT main upper bounds also remain open. Classical finite selection is not an executable polynomial-time implementation.

This is a bounded independent component review of the exact frozen packet, not a final audit or a full-paper completion claim.
