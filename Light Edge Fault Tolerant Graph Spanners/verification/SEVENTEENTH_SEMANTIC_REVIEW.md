# Seventeenth bounded semantic/source review

Date: 2026-10-11 UTC.

Verdict: **COMPONENT PASS for the seven frozen modules. No semantic blocker found within this scope.** This verifies conditional native quotient/counting and terminal obstruction components. It does not establish general tree packing, the full exchange construction, or the paper's main upper bounds.

## Scope and checkpoint integrity

I reviewed all 459 lines of the seven production sources, their relevant previously reviewed partition, cut, bridge, forest-cardinality and refinement dependencies, Mathlib's actual native graph definitions, and the pinned Kaiser text. I made no production changes, invoked no compiler or checker, and performed no publication. The only file written is this report. Build and replay findings below concern inspected existing evidence, not newly executed verification.

The frozen review manifest, production manifest, working source bytes, and the local Git contents of checkpoint `9c2e5d14206573748e1054040807f84d24d680da` agree exactly:

| Module | SHA-256 |
|---|---|
| NativeCorePackingCriterion | 6823faa67c1617b68258376828a742a3b589211f0be1f472ec23e7a41d8e6f54 |
| NativeForestQuotient | d8d54ad21dd2906d66c8b53c55b1ff3c92bab2a92c8b055d32a3b33feed45a19 |
| NativeQuotientCardinality | af4f070ab7d4df55bbfebf903c1a6915d02c58188d9d8fa67de55c54aea18699 |
| NativeQuotientReachability | 5dfa73d01b5874881663d7abe688c473086e35ad2a7327c462026fe8c7abdd46 |
| NativeCrossingNonbridge | 474ae376273d59b18c2f631c2834eb86c3a5d5c7c7b4502b1740ec3dd98f3180 |
| NativeColorCrossings | bd3e1344c81c61020c90201bebeac118ad455fde81e2a6fd97f8bbafb2ef424c |
| NativeTerminalDensity | db7f8b77f4a02bc207ac9d7b61d79cf3a0c74441f979bda71d40040a619265d9 |

Every one of the 78 production Lean module files at reviewed baseline `1d33c9e705ad48570d4f9787b5e19e8a7a1c475c` is byte-identical both at the new checkpoint and in the working tree. Earlier reviews are inherited by this equality; they were not repeated in full. The proof-source diff adds exactly these seven files and their seven root imports. There are exactly 85 production modules and exactly 85 distinct root imports, with no omissions or extras. The repository was clean during inspection. Both local HEAD and the locally recorded remote-tracking branch point at the supplied checkpoint. The parent's fresh publication/read-back report is consistent with these contents; this review did not independently refresh the live remote or CI.

## Recorded validation and its limits

The local and committed copies of all four seventeenth gate logs are byte-identical, including their contents at the checkpoint. The inspected strict-build scripts use `set -euo pipefail` and `-DwarningAsError=true` for each new module; the Lean wrapper also supplies `-DautoImplicit=false`. The first group covers four modules, and the second covers the remaining three, the aggregate root, module-index check, and axiom audit. Recorded completion times are 00:07:37 and 00:09:34 UTC.

The second build log records the exact 667-declaration audit, permitting only `propext`, `Classical.choice`, and `Quot.sound`, followed by index success and `SEVENTEENTH_AGGREGATE_GATE_PASSED`. Inspection of the audit source confirms it identifies declarations by their owning project module and examines collected transitive axioms. No placeholder proof, custom axiom, unsafe declaration, or implementation override appears in the seven reviewed sources.

Both replay scripts use the official `leanchecker` wrapper; the committed logs contain individual successful replay markers for all seven modules. Recorded replay completion times are 00:10:57 and 00:12:37 UTC. These records corroborate the supplied successful local gates. Earlier 78 compiled objects were reused. This is **not** a clean full-85 local rebuild, and it is **not** a claim of successful remote CI for the exact 85-module checkpoint. Those remain separate validation gates.

## Semantic findings

### 1. Induced-core partition criterion

`induced_core_crossings_eq` identifies the same original identities on both sides. The forward direction sends actual induced endpoints to their `some` images. The reverse direction unpacks actual original witnesses of a mapped link; its non-outside labels force both original endpoints into the core. Outside-boundary edges and loops at the collapsed outside vertex therefore do not contaminate the internal crossing count. The equality itself correctly needs no inclusion hypothesis: its link witnesses already come from the original graph.

Mathlib's native `induce K` has vertex set exactly `K`, even when `K` contains ambient nonvertices. Consequently the inclusion hypothesis in `native_core_treePartitionCriterion` is essential and is present. It proves `G.induce K ≤ G`, so the result really concerns a native subgraph with actual vertices. The previously reviewed minimal-core cut budget gives the partition inequality for every surjective labeling with more than one block. Empty and singleton label sets are handled separately using natural-number subtraction, rather than smuggling in a nontriviality instance. Empty or singleton cores introduce no false connectivity or existence assertion.

The hypotheses remain the integral cut bounds `|δ(K)| ≤ 2k` and `|δ(A)| ≥ 2k` for every nonempty proper subset, plus actual-vertex inclusion. This supplies the genuine induced-core tree-partition premise. It neither assumes nor proves general packing, and does not upgrade the already-scoped integral CS09 foundation to a weighted/fractional result.

### 2. Connected-fiber contraction and native bridges

The fiber hypothesis is actual reachability in `blockGraph` of the original surviving adjacency graph, with equality of labels at each permitted step. It is not ambient connectivity or a relation named "connected." For a crossing original edge, any within-fiber adjacency witness must be a different identity: the native same-edge endpoint-uniqueness property would otherwise contradict its unequal labels. Thus every within-fiber path survives deletion of that precise edge, including when other identities are parallel.

A singleton bridge cut is then constant on every fiber, because paths after deleting that cut cannot switch sides. The pushed cut uses `f '' (S ∩ G.vertexSet)`, not an image of arbitrary ambient vertices. Fiber saturation proves exact equality of original cut identities. This establishes that a crossing bridge remains a bridge in `G.map f` and subsequently in the crossing-edge restriction.

Inspection of Mathlib confirms `map` preserves the edge type and edge set and uses actual endpoint preimages; its vertices are exactly `f '' G.vertexSet`. `restrict` preserves all those vertices. Hence `crossingQuotient` removes internal edges after mapping, keeps isolated image vertices, and retains distinct crossing parallel identities. The all-bridges conclusion is a genuine native-forest condition: the earlier proved characterization excludes loops and parallel cycles before simple-graph counting. It does not infer native acyclicity merely by forgetting multiplicity.

### 3. Actual quotient vertices, projection, and tree cardinality

`quotientVertex` carries an actual original vertex to a certified image vertex, whether or not that vertex has an incident crossing edge. Walk projection treats an internal step by equality/reflexivity and a crossing step by its original identity, then concatenates the resulting walks. The connectedness proof obtains a quotient inhabitant from an actual original inhabitant and explicitly finds original preimages for both quotient endpoints.

`tree_crossingQuotient_card` combines that connectedness with genuine preservation of all crossing bridges and the previously proved native tree count. The right side is the actual image subtype, not the ambient target cardinality. `[Finite W]` supplies the necessary finite target; no finiteness of unused ambient vertices is silently counted. Connectedness rules out the empty image in this theorem. A one-vertex quotient correctly has zero crossing edges. Connectedness of every fiber is an explicit essential premise, preventing disconnected identifications from creating new native cycles.

### 4. Quotient walk lifting and disconnection preservation

The lifting proof quantifies over chosen original endpoints and equations identifying their quotient vertices. Its empty-walk case uses genuine same-fiber connectivity between those endpoints. For a nonempty quotient walk, it extracts an actual original identity and original link witnesses, connects the chosen start to the witness inside its fiber, traverses that original link, and applies the induction hypothesis at the next chosen original endpoint. Subtype equality and endpoint-image equations explicitly perform the dependent vertex transport.

This is real lifting of reachability, not a definitional renaming or assumed converse. The contrapositive therefore legitimately keeps an unreachable original pair unreachable after contraction of connected fibers. All claims concern actual vertices; phantom target elements never become quotient endpoints.

### 5. Crossing native nonbridge and same-identity deletion alternative

The density theorem first transports the actual unreachable pair into the quotient and invokes the previously proved native disconnected-forest deficit. A resulting quotient nonbridge is unpacked to a present original identity with endpoints of different labels. If that identity were an original bridge, the proved connected-fiber bridge transport and restriction theorem would contradict its quotient nonbridge status. Finally, the native bridge/deletion equivalence yields actual reachability between its original endpoints after deleting that very identity.

This handles a parallel-edge cycle correctly: another parallel identity may provide the alternative. A loop cannot be chosen because its endpoint labels cannot differ. The output is a genuine alternative reachability witness (a nonempty walk proposition), not a formally packaged native cycle or a minimum-level cycle edge. The original alternative stays in the stated graph after identity deletion.

The generic lemma allows an infinite ambient edge type, but its finite-target density premise uses `Nat.card`. If the crossing edge set is infinite its `Nat.card` is zero, while the preserved unreachable pair forces at least two actual image vertices, so that density premise cannot hold. This is sound; it is not an infinite-edge density theorem. The terminal application has explicit `[Fintype E]`.

### 6. Exact original-identity color accounting

`crossingIdentities` and `actualPartitionCrossings` coincide by explicit conversion between ambient endpoints with actual link witnesses and actual vertex subtypes. The quotient edge set is proved equal to precisely that finite identity set. Color restriction selects exactly its color fiber, and the finite fiberwise cardinality identity sums those disjoint fibers to the full crossing set.

The total color function assigns every actual original identity exactly once. Values on nonedges do not affect any count. Loops never enter the crossing set; different parallel identities remain distinct summands even when their endpoints and colors agree. No arbitrary family of numerical counts or assumed partition identity replaces the graph semantics.

### 7. Terminal last-color obstruction

Surjectivity is from `G.vertexSet` onto `Fin m`, so every one of the `m` labels is an occupied block. Each color restriction retains that same actual vertex set. For the first `k` colors, the explicit native-tree and connected-fiber premises give exactly `m - 1` crossing edges. The exact color-sum theorem, combined with `TreePartitionCriterion G (k + 1)`, forces at least `m - 1` crossings in the last color, equivalently the displayed density bound. Natural-number edge cases, including `m = 0`, are handled without illegitimate cancellation.

The final theorem additionally assumes within-fiber connectedness in the last color and an actual unreachable last-color pair. Applying the generic nonbridge theorem to this last-color restriction yields an original `G.IsLink` witness, the last-color identity equation, unequal block labels, native nonbridge status in that color, and an alternative in that same color after deleting that same original identity. It does not accidentally return an edge or alternative path from another color or merely from the ambient graph.

The first-color trees and all-color fiber connectivity are induction-step premises, not a hidden assumption of the desired full packing. The theorem is conditional on supplied finite labels and surjectivity. It does not itself construct those labels from the previously developed terminal setoid iteration or discharge the first-color induction hypothesis. Such integration remains part of the full packing construction.

## Source correspondence and remaining boundaries

The pinned primary source is Tomas Kaiser, *A short proof of the tree-packing theorem*, arXiv:0911.2809v3, 6 March 2012, https://arxiv.org/pdf/0911.2809v3. I checked both local source hashes against `review/tree-packing-proof-route.md`: PDF `4bef0841bbfe41cc93c2edfa33ec6649c56f7810e6e5dc932e053dec1a85808b`; text `58342327af7f9d3cd5586549b12eb2ea53ab7018fc2a557dc6fc3859ffcde506`.

The construction matches the page-3 terminal argument: contract connected terminal blocks, count each existing tree quotient exactly, subtract their edge counts from the full partition lower bound, preserve last-color disconnection, and force a crossing edge with an alternative route in the last color. The Lean indexing uses `k + 1` total colors and `k` initial trees; the source uses `k` total colors and `k - 1` initial trees. These are consistent reindexings. Original loops and parallel identities have the intended source semantics throughout.

The packet improves the earlier generic density witness to an actual crossing last-color nonbridge with same-identity deletion reachability. It still does not supply a native cycle object, connect that witness to a minimum finite level, construct the full tree exchange, prove the required lexicographic order/maximal choice and contradiction, or establish general Nash-Williams/Tutte packing. New drafts `NativeEdgeLevels` and `NativeNonbridgeCore` are outside this freeze and were not reviewed. Mader splitting, general Steiner-forest construction and expansion, weighted/fractional external scope, optimized sampling, full runtime, and the main upper bounds also remain open.

**Disposition:** accept the seven-file checkpoint at the stated component scope. No requested proof-source correction is needed. Preserve the explicit induction/fiber premises and the separate clean-build/remote-CI limitations in any downstream status report.
