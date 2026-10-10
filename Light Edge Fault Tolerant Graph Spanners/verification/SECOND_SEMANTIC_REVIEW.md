# Independent second semantic review

Reviewed 2026-10-10 UTC. Scope: the eight frozen modules below and the definitions/proof dependencies needed to interpret their statements. This was read-only except for this report. No compiler, replay, shared compiler lock, or external write was used.

## Judgment

No semantic blocker found at these hashes, within the assigned scope. The actual complete-bipartite counterfamily and optimal-denominator bounds follow from graph/walk/counting arguments rather than assumed final inequalities or oracle certificates. The foundational results match their narrower assigned claims.

This is not a whole-paper audit, a kernel/build/replay result, or completion/publication permission. Full tree packing, graph pruning, probabilistic lightness analysis, runtime, and asymptotic lambda contradiction remain outside these modules.

## Frozen source identities

All eight SHA-256 hashes were independently recomputed and matched `second-source-hashes.json` immediately before this report:

- `MetricSemantics.lean`: `8dc1f9c4b511b988327c33620fed46a46e642b63e4632bcb36c8c51893dbde29`
- `MissingEdgeConnectivity.lean`: `575ba0a68eaa5bfb7658eb857f6534c365fd317114e344b7fd2eee144f9cda24`
- `HostCounting.lean`: `634e0e198a85dca14489cebfbe189dc597e610876626496f52c85642c8b520ae`
- `Blocking.lean`: `9760ed756dcd3737d3a94cec4671916b27a3cfff0deabc314fed9538ce9a350f`
- `TreePruning.lean`: `31ce849753f434d4ece5b2c839f075228640f9b768a2f46a9a455b95ce7429d9`
- `HubPreserver.lean`: `206ac13a0cba5b5cc938592350046779693cbc0fa371d08df820fedd2d16b892`
- `BipartiteForcing.lean`: `9ec351fe8d6707afc3db61bc818318d7a84b2474ae956ed417fc104b3e92c5bf`
- `CounterfamilyWeight.lean`: `0f498e55963f03c00e752995ba879faf590c4766bc0ab6fb084d79a651d8ea86`

## Actual counterfamily

### HubPreserver: accepted

The graph is an actual simple graph on L ⊕ R, containing exactly cross edges incident to a left hub in A or a right hub in B. It is proved to be a subgraph of the complete bipartite graph. Injectivity of the cross-edge map L × R → Sym2(L ⊕ R) prevents conflating the disjoint sides even when their underlying types coincide.

The clean-hub arguments inject purportedly contaminated hubs into distinct failed cross edges. Fewer faults than hubs yields a clean hub on each side. Every left vertex connects to the clean right hub, every right vertex to the clean left hub, and the hubs connect to one another. Connectivity is thus proved after every allowed F, including empty faults, failures outside the certificate, and extraneous nonedges. This connectivity and subgraph monotonicity prove the actual connected-component equivalence for every vertex pair.

### BipartiteForcing: accepted

Unit walk weight is its actual length. A walk between opposite sides of a bipartite subgraph with length below three must use the direct edge; length-zero and length-two possibilities are excluded by the disjoint vertex constructors. Applying the EFT condition at F = ∅ to each one-edge input walk forces every cross edge for t < 3. The reverse containment is part of the spanner definition. Spanner fault budget f is arbitrary here and is not confused with the competition budget.

Although t < 1 can make the general premise impossible, the explicit wrappers use real stretch 5/2 and f = 1. Their eligible class is nonvacuous: the full graph satisfies the replacement condition after every fault set by using the identical walk of nonnegative unit weight. This is a mathematical observation here; the wrappers do not separately state existence of H.

### CounterfamilyWeight: accepted

Total weight is the imported sum over the actual unordered edge finset. The complete graph's edges are the injective image of L × R, giving weight |L||R|, hence m². The certificate's actual edges lie in the union of A × R and L × B, so its weight is at most |A||R| + |L||B|. Exact intersection subtraction is unnecessary: r hubs per side give the sufficient bound 2rm.

The imported minimum-preserver definition demands actual feasibility and comparison with every feasible graph. Existence minimizes over the finite set of simple graphs, with G itself feasible. It assumes neither an optimum value nor certificate. Positivity is proved separately: at empty faults, a feasible preserver must connect vertices on opposite nonempty sides, so it has an edge and strictly positive unit total weight.

For 0 < r ≤ m, the proof selects an actual r-element subset A of Fin m. Its hub graph survives every (r−1)-fault set. Optimal weight is therefore at most that certificate's weight, hence at most 2rm. Rewriting H to the complete graph gives m² in the numerator. Positive denominator permits division in the correct direction: m²/OPT_(r−1) ≥ m/(2r). The final inequality, denominator positivity, and certificate feasibility are not assumptions in the explicit wrappers.

The wrappers take r=3 and r=4 with m≥3 and m≥4 respectively. They choose a true optimum Q first, then quantify over every actual 1-EFT stretch-5/2 output H, yielding m/6 at competition budget 2 and m/8 at competition budget 3. The numeral 5/2 is real through its expected stretch type. Fault tolerance 1 remains separate from denominator budgets 2 and 3. The imported uniqueness theorem shows all minimizing Q have the same weight.

## Other foundations

- **MetricSemantics: accepted.** Distance is an actual ENNReal infimum over weighted walks. The imported equivalence obtains a minimum path on finite vertices by removing nonnegative detours and minimizing over finite simple paths. Unreachable pairs have infinite distance. Nonnegative weights and positive real t justify the reverse implication and multiplication by infinity. Same-vertex-set subgraphs inherit the same weights. The all-finite-unordered-pair fault convention is equivalent to the paper's input-edge convention by intersecting F with G's edge set; this leaves G and its subgraph unchanged after deletion and cannot increase cardinality. The module states the all-pair-set version, without a separate formal normalization theorem for the paper convention.
- **MissingEdgeConnectivity: accepted.** The imported missing-edge lemma correctly erases the absent edge from F before invoking preservation; deletion in Q is unchanged while the input edge survives. Native IsEdgeReachable(f+1) really quantifies deletions of cardinality below f+1. The degree consequence is native, and strict neighborhood inclusion proves the maximum-degree corollary. No disjoint-path packing is assumed or constructed.
- **HostCounting: accepted as conditional counting/algebra.** Actual incidence sets and a union bound count blocked hosts; congestion two yields h good hosts from 2f+h indices and at most f blockers. Weighted incidence counts indexed multiplicities. The ratio theorem explicitly assumes positive seed weight and h, plus multiplicity/per-host/congestion bounds, and retains additive baseline 1. It does not prove these graph inequalities or construct a packing. Identical tree contents can have distinct indices, with congestion still measured over those indices.
- **Blocking: accepted for actual seeded greedy.** Tail-first recursion on a descending list processes edges in ascending weight. Actual rejected tests supply bounded old-edge fault witnesses; these define ordered pairs with both entries in the output graph, first entry outside the seed, no self-pair, and cap f. A cycle's exact complementary walk contradicts rejection unless it contains a witness fault. Induction handles cycles avoiding the new edge. Weak weight inequalities plus recursion order handle ties. The stronger cycle condition implies Lemma 20 when a maximum-weight cycle edge is outside the seed and weights allow the paper's normalized-weight reading. The finite wrapper uses actual sorted input and output, not a blocking oracle.
- **TreePruning: accepted only as the cycle-maximum exchange fact.** The tree is actual and the edgewise HasBottleneckPaths hypothesis supplies, for each input edge, a tree walk using no heavier edge. A tree maximum on a cycle defines a cut; if every maximum were in the tree, the complementary cycle would cross through a strictly lighter edge, contradicting its bottleneck tree walk. Tied maxima are handled explicitly. This hypothesis is stronger than merely minimizing the tree's single largest edge. The module does not construct the pruned graph or prove all of Lemma 26.

## Paper correspondence and scope limits

Read the independent lambda audit and pinned paper text around Definitions 1, 5, 7–8 and 19, Theorems 11–13 and 17–18, Lemma 20, and Lemma 26. The displayed upper statements include positive integer f=k=1 and epsilon=3/2, yielding actual stretch 5/2 and displayed lambda argument 5. The competition budgets correspond to 2f and (2+eta)f with eta=1. These modules impose no global small-epsilon or k≥2 restriction.

The modules prove the linear lower-bound ingredient. They do not define lambda, prove lambda(2m,5)=O(sqrt(m)), encode the asymptotic contradiction, or replace the separate source audit. They support correction of the exact displayed lambda upper comparisons without refuting coarser polynomial bounds or the 2f competition threshold.

Imported project definitions inspected: LightEFTSpanners.Basic, SeededGreedy, ConnectivityOptimum; LightSpanners.Basic, Distance, Weight, MinimumTree, and relevant TreeReduction declarations. The native edge-connectivity definition and degree lemma were also inspected. Transitive imports were not exhaustively audited. Source inspection found no proof holes, axiom declarations, opaque substitute results, or unsafe execution in the eight modules and directly inspected EFT dependencies; this is not a transitive kernel axiom audit. Build, axiom audit, fresh replay, CI, and subsequent source changes remain separate gates.
