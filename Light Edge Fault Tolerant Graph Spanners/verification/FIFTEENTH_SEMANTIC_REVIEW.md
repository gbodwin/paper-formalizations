# Fifteenth semantic review: native forest foundations

Reviewed 2026-10-10 UTC. **PASS for the four-file single-forest/tree foundation scope.** No semantic blocker found. This is not a general packing theorem, splitting theorem, full-paper audit, or fresh full-repository build attestation.

## Frozen artifact and independent identity checks

Exact proof checkpoint: `117130f1621f40a39749d0dc27145cdb4f2d4a71`, branch `light-eft-spanners-checkpoints`, repository `gbodwin/paper-formalizations`.

The reviewer independently fetched each of the four files through the GitHub connector at that exact commit. Each returned UTF-8 byte sequence equals both its local production file and its `git show` checkpoint blob. SHA-256 was independently recalculated and agrees with both `review/fifteenth-source-hashes.json` and the published-project `verification/FIFTEENTH_SOURCE_HASHES.json`. The returned Git blob IDs were independently recalculated too:

| Module | SHA-256 | Published Git blob |
| --- | --- | --- |
| NativeBridgeSemantics | `605bacebc42d3d5b75713dc1444840065cd7a2265f340659e1f38a4e6a69f948` | `a49bbb1afdcd8b87a8b04c521516c03a2d2906ec` |
| NativeForestSemantics | `988a65afe1048cb78445504c137576dbea55963ecbd4497aed4e1b6c6d7bfedd` | `956f143eed0b5a6ffd12f80d6a1a10a4ec68b8a5` |
| NativeForestSelection | `c6d001e26d26f70b6197f1cb66401b8931414bd3d5301a0694904725596405c6` | `bc84fe584e32b5cbf1acab9f5cf4653150a091f9` |
| NativeForestCardinality | `1efc991892150e4d7a1c43a22b4b559c7a9a86797fb8f3a85adb6a579b4fd0f7` | `793f4e4be5628822feab0847dba18c2c234acbeb` |

All **68 prior production proof files** are byte-identical between the current working tree, this checkpoint, its direct parent `36d27d9d847d2a2b1e4e00ab44800bd4addd1948`, and the brief's earlier baseline `c3a3aae006f140cfb1b007974320f0d3b3ea90d6`. Thus the two baseline references in the assignment and brief cause no proof-source discrepancy. Production now contains 72 module files. The production repository was clean when inspected.

Published sources: [bridge](https://github.com/gbodwin/paper-formalizations/blob/117130f1621f40a39749d0dc27145cdb4f2d4a71/Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/LightEFTSpanners/NativeBridgeSemantics.lean), [forest semantics](https://github.com/gbodwin/paper-formalizations/blob/117130f1621f40a39749d0dc27145cdb4f2d4a71/Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/LightEFTSpanners/NativeForestSemantics.lean), [selection](https://github.com/gbodwin/paper-formalizations/blob/117130f1621f40a39749d0dc27145cdb4f2d4a71/Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/LightEFTSpanners/NativeForestSelection.lean), [cardinality](https://github.com/gbodwin/paper-formalizations/blob/117130f1621f40a39749d0dc27145cdb4f2d4a71/Light%20Edge%20Fault%20Tolerant%20Graph%20Spanners/LightEFTSpanners/NativeForestCardinality.lean).

## Semantics checked directly

I read the actual installed mathlib definitions, not just the project comments: `Graph` in `Graph/Basic.lean`; restriction/deletion in `Graph/Delete.lean`; simplicity/projection in `Graph/Simple.lean`; native cuts/bridges in `Graph/Connected/EdgeCut.lean`; and the relevant simple-graph deletion, reachability, connectedness and acyclicity sources.

- A native edge identity has one unordered endpoint pair, endpoints must belong to the actual vertex set, and every member of the edge set has endpoints. `restrict` preserves the entire actual vertex set definitionally, keeps the intersection of original and selected edge sets, and preserves original incidence. `deleteEdges` removes individual original identities before projection. `toSimpleGraph` has vertex type `G.vertexSet`, not the ambient type, and adjacency means distinct endpoints with an actual native edge.
- Native `IsBridge e` is existence of an actual cut exactly equal to `{e}`. `not_reachable_cut_subset` constructs the post-deletion reachable component and shows any native edge crossing its boundary was deleted. It does not assume a cut, packing, count, or conclusion-shaped witness. `bridge_iff_not_reachable_delete` uses the explicit incidence premise to give precisely the expected endpoint-disconnection equivalence.
- Loops cannot be bridges because the endpoint reaches itself after deletion. Two distinct parallel identities cannot both satisfy the all-bridge condition: both cross any separating endpoint cut. The direct proof of simplicity establishes both facts before any forest conclusion. Irrelevant identities outside `G.edgeSet` are never required to be bridges or selected.
- The one-sided simple-deletion/native-deletion inclusion is valid without simplicity. The reverse inclusion requires `G.Simple`, and its proof uses uniqueness of the actual native identity for each endpoint pair, in both orientations. Consequently `all_edges_bridge_iff` correctly concludes and requires **simplicity plus projected acyclicity**. It does not mistake acyclicity after collapsing parallel edges for multigraph acyclicity. Mathlib's simple-graph bridge predicate can also hold for disconnected nonedge pairs, but these proofs invoke it only on actual adjacency edges; that potential pitfall is avoided.

## Selection and genuine existence

`edgeRepresentative` chooses once per unordered element of `Sym2 G.vertexSet`, with actual edge membership required. Its specification handles both endpoint orientations. Proof arguments do not introduce different choices for the same unordered edge: they are propositions, hence proof-irrelevant. `edgeRepresentative_endpoints` uses native uniqueness of endpoints, and `edgeRepresentative_injective` prevents one identity from representing different unordered edges.

Every supplied `H` has an explicit `H ≤ G.toSimpleGraph` premise. `representativeSet` is exactly the image of the genuine edges of `H` under this common representative choice. `selectNative_simple` excludes loops and parallel selected identities, and `selectNative_projection` proves equality to `H` in both directions. This is not an arbitrary abstract forest detached from native incidence.

`exists_native_spanning_forest` then constructs an original-edge subset, proves it is contained in the actual original edge set, proves every retained edge is a native cut bridge, and preserves the complete reachability relation. Vertex preservation follows directly from native restriction, including isolated vertices. It needs no finite, inhabited, connected, or full-ambient-vertex hypothesis.

The imported existence result is a genuine mathlib proof: `exists_isAcyclic_reachable_eq_le` starts from the empty simple subgraph, extends it to a maximal acyclic subgraph through Zorn's lemma, and proves maximality preserves reachability by adjoining an edge between distinct components. I inspected this chain, including `exists_maximal_isAcyclic_of_le_isAcyclic` and `reachable_eq_of_maximal_isAcyclic`. It is not a newly introduced axiom or a passed-in existence oracle. Classical choice is used openly, so this is an existence construction rather than an executable forest algorithm.

## Cardinalities, premises and boundary cases

`simpleEdgeEquiv` proves an actual bijection between simple adjacency edges and original native identities. Injectivity uses representative injectivity; surjectivity takes each original edge's endpoints, excludes a loop through native simplicity, and uses native identity uniqueness. The unrestricted `Nat.card` equality is backed by this bijection, not by coincidental zero values on infinite sets.

`native_tree_card` assumes only finite actual vertices, all actual edges bridge, and actual projected connectedness. Native simplicity follows from the bridge hypothesis, so finite simple-edge cardinality transfers to native identities. It invokes the forward direction of mathlib's genuine finite-tree counting theorem, whose underlying proof uses the unique paths of a tree and a finite bijection; no edge-count formula is assumed.

`exists_native_spanning_tree` starts with only finite actual vertices and connectedness. It obtains the forest above, transfers connectedness using the proved reachability equality, and obtains its count from `native_tree_card`. The equality `(G.restrict F).edgeSet = F` is justified by the proved `F ⊆ G.edgeSet`, so the result counts the selected original identities themselves.

`native_connected_card_lower` additionally and appropriately assumes finite actual edges: without this condition, `Nat.card` of an infinite parallel-edge set could be zero. Its bound follows from the constructed tree's count and an explicit inclusion injection into the original actual edge set. Neither ambient vertex nor ambient edge types need be finite.

Boundary checks from the definitions/proofs: empty and disconnected native graphs are admitted by arbitrary-graph forest/selection statements; isolated vertices persist; a loop-only singleton selects no loop and has the correct zero-edge tree; two parallel edges select at most one common unordered-edge representative. Mathlib `Connected` explicitly includes `Nonempty`, so empty graphs cannot accidentally trigger the tree count `0 + 1 = 0`. Singleton connected graphs are admitted. Ambient phantom vertices do not enter any count. These are semantic checks, not newly compiled test lemmas.

## Validation boundary and verdict

The four files contain no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`. I inspected the strict-build script, the exhaustive module-origin-based axiom-audit implementation, the official `leanchecker` wrapper, and the saved build/replay logs. The logs record all four strict production builds, the root/index gate, 577 declarations using only `propext`, `Classical.choice`, `Quot.sound`, and all four successful official kernel replays. This review did not rerun the compiler or take the compiler lock, and does not upgrade those incremental checks to a fresh full-72 rebuild or attest to exact CI completion.

**Conclusion:** accept this checkpoint as a sound native original-identity single-spanning-forest/tree foundation. No requested source correction is needed. General Nash-Williams/Tutte or Eulerian forest packing, Mader splitting, weighted/fractional source assumptions, and the paper's full upper bound remain outside what these four files establish.
