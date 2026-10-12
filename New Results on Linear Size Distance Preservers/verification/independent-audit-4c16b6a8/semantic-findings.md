# Independent semantic review of the accepted corrected distance-preserver results

Target: commit `4c16b6a8a6d208795f6e099bc2df534923d22958`, tree `3dd51cd13c57fcce3b5b5bcd2851fab9299ce941`.
Original: Greg Bodwin, *New Results on Linear Size Distance Preservers*, arXiv:1605.01106v4 (30 December 2020). Both supplied original TeX and extracted PDF text were inspected. All source locations below refer to the frozen candidate, not a moving branch.

## 1. Claim inventory and mathematical scope

The source has four main theorems (1–4), auxiliary Theorems 5–6, Lemmas 1–7, Definitions 1–8, and three open questions. The accepted statement map covers each numbered theorem and required helper. The corrections are substantive and must travel with the completion label. In particular, the accepted final conclusion of Theorem 4 is the 3/4-log-deficit statement; this audit does not treat the original stronger square-root-deficit assertion as an outstanding accepted deliverable. Nor does it certify or refute that original existential assertion.

The accepted contract does not hide an additional missing main edge bound. It accurately distinguishes mathematical existence from executable algorithms, source helper replacements from literal lemma proofs, and corrected domains from impossible degeneracies.

## 2. Theorem 1 and the directed distance model

`PathUnion.lean` defines an actual directed list walk by its endpoints and every consecutive adjacency, cost as the sum of those edge weights, and distance as the infimum of all walk costs in the extended nonnegative reals. It does not define a preserver by a supplied bound or a fake distance. `NativeWalkBridge.exists_native_walk_le` bridges to native walks in the complete ambient simple graph, erasing only self-loops with nonnegative cost. The ambient graph is not used to permit disallowed directed steps: `Allowed` checks each dart against the original relation.

`ConsistentTiebreaking.exists_optimal` minimizes a real-cost/edge-code lexicographic score over the finite set of simple allowed paths. `score_bypass_le`, `score_injective_on_paths`, and `optimal_subpaths_eq` prove attainment, uniqueness of the tie-breaker and subpath consistency. Thus the final root does not ask its caller for shortest routes or consistency.

`Branching.Routing` assumes predecessor/rank consistency, not an edge bound; `RoutingOfPaths` constructs this interface from the chosen native paths. `branch_vertex_unique` is the three-path combinatorial argument. `excess_card_le` injects excess incoming edges into ordered path triples, giving `edges_card_le`: E ≤ 2n+p³. `Batching.integer_theorem_one` performs the cube-root partition with explicit rounding, yielding 3n+24p floor(cuberoot(n))². This is the original O(n+n^(2/3)p) rate with uniform constants.

`TheoremOne.theorem_one` constructs the finite actual edge subset. Its unreachable branch changes the auxiliary target to the source only for routing, then proves the original demanded distance remains infinity by subgraph monotonicity. Empty V, zero weights, loops, repeated demands, and self-demands are not excluded. Signed or infinite edge weights are excluded by NNReal and are not certified.

The source's sharper Lemma 3 count of binomial(p,3) branching triples is not proved literally. The sufficient p³ replacement is explicitly disclosed and retains the main theorem. No hidden inference from the sharper unproved count is used.

## 3. Theorem 2, lazy trees, averaging, and the RS extremal number

`LazyTreeSelection.Valid` is a concrete parent map: roots have no parent, a parent-child edge is in G, graph distance strictly increases by one, selected nonroots have a selected parent or the root, and reachable demands are selected. Finite minimization first minimizes support, then single-child parents. The reroute argument proves laziness; deletion of an unnecessary leaf proves leaf inclusion. The selected support forms the rooted tree; unused vertices remain isolated in the graph on V.

`tree_walk` and `tree_preserves` establish native extended-distance preservation, including unreachable demands. `exists_lazy_tree` supplies the parent map internally. It does not assume a tree or an endpoint-distance conclusion. The original exact leaf equality is false on root–a–b with demands at a and b. The corrected nonroot-leaf inclusion is sufficient for `branchEdges_le_two_demands` and is disclosed. The finite optimizer is not an O(n²)-round executable procedure; neither such rounds nor bit/RAM runtime are claimed proved.

`FavorableCut.exists_favorable_cut` proves finite averaging over vertex colorings, retaining at least 1/4 of eligible oriented edges. `TheoremTwo` assigns a single owner to overlapping nonbranching edges. `InducedMatchings` and `MatchingExtremal.lazy_partition_bound` use three depth residues and the surviving bipartite cut to obtain actual induced partitions, with no caller-supplied partition oracle. The final H is the undirected union of the chosen parent edges; actual distances and E ≤ 2|P|+12M(V) are proved.

`matchingNumber` is an actual finite supremum over oriented loopless edge sets partitionable into labels indexed by V. `Separated` forbids shared vertices and all cross edges within a matching. It is the intended maximum induced-matching extremal edge count, not the reversed sparse-graph implication in the original prose. `InducedMatchingRemoval` explicitly constructs tripartite triangles, proves their edge-disjoint/no-accidental properties, and invokes mathlib triangle removal to prove the epsilon/threshold subquadratic statement. Empty/singleton graphs are legitimate. The cited sharp quantitative literature estimates for RS are not re-proved or assumed as axioms.

## 4. Weighted Theorem 3 and its asymptotic consequence

`ModularGraph` and `ModularPerfect` construct actual undirected modular-layer graphs. The repaired weight is k*x²+1+a². `QuadraticRepair.constant_slope_unique_shortest` handles every signed direction sequence: extra steps incur the baseline, while a k-step competitor must be entirely forward, allowing the modular displacement equation to become an integer equation and the squared-deviation identity to force a constant slope. This does not repeat the invalid Euclidean wraparound argument.

`WeightedNativeForcing` and `PreserverForcing` identify native path cost with the true walk infimum, obtain attained shortest walks in equal-distance subgraphs internally, and force all covered edges. Preserver hypotheses quantify all actual subgraphs; they are not premises asserting the desired edge bound. H=G always satisfies distance preservation.

`TheoremThreeExact` internally selects integer parameters, uses a path witness for small ranges, and pads by isolated vertices/enlarged terminal sets using metric-preserving injection/comap lemmas. `bounded_range_lower_bound` fixes C>0 and works for every exact N,T with 2≤T≤N and T³≤C³N². It returns G on Fin N, exactly T terminals, and positive symmetric finite edge weights, forcing T³N²≤(32768C)³E³. Consequently E≥T*N^(2/3)/(32768C). C can absorb any fixed original O-range constant.

`WeightedSuperquadratic.superquadratic_weighted_little_o` uses the actual real little-o predicate. For a terminal-count sequence eventually at least two and at most N, T=o(N^(2/3)) implies that every fixed real B is eventually exceeded by E/T² in exact-size witnesses. B occurs before the eventual threshold; the graph and weights are constructed, not caller-supplied. The finite bound already gives witnesses independently of an arbitrary presumed superquadratic conclusion. A singleton cannot support a nonzero subset lower bound, so the stated lower endpoint is necessary.

## 5. Theorem 4 displayed rate: uniformity and geometric assumptions

`UniformDimension.uniform_dimension_lower_bound` has only finite numeric domain hypotheses: A≥0, N≥8, 2≤T≤N^(2/3), 2≤d≤A sqrt(log N). Its coefficient-one loss exp(-(1004+7A)sqrt(log N)) is common in N,T,d once A is fixed. It has no residual capacity, selected scale, direction-family, lattice-count, or geometric-certificate input.

The proof really handles three regimes. The planar case is obtained from primitive-direction convex chains, independent integer scales, and native graph forcing. Small higher dimension d³≤sqrt(log N) uses balanced lattice geometry, absorbs the explicit d^(1000d²) factor, and obtains the 1004 loss. Larger dimensions use the elementary-sphere family with an exp(7d) coefficient and the exact polynomial comparison. These branches are exhaustive; there is no fixed-dimension constant silently reused across growing d.

The sharp lattice quantity is the extreme-point set of the convex hull of the actual finite integer ball (`LatticeHull.vertices`, `ball`, `mem_ball`, `image_vertices`). It is connected to the Euclidean body used by volume through `LatticeBody.image_vertices` and `LatticeApproximation.convexHull_vertices`. Approximation lower bounds and the proved shallow/deep cap missed-volume upper bound yield `LatticeVertices.uniform_vertices`. `BalancedVolume`/`BalancedRadius` additionally give a dimension-explicit radius and coefficient. Thus the old conditional helpers are discharged at the final root, not postulated. Translation of extreme points proves average rigidity, the property needed for unique layered paths; it does not assert equivalence to the source's stronger sum-at-most-one description of convex position.

The outer Behrend capacity, inner scales, baselines for small parameter values, and padding are chosen by internal lemmas (`terminal_scales`, `parameters_or_baselines`, `SphereScales.exact_size_lower_bound`, `HigherProduct`). The displayed formal domain is at least as broad as the source's sufficiently small terminal subrange. This establishes the original displayed edge-rate form with the stated corrected conventions.

## 6. Accepted Theorem 4 terminal consequence and nonvacuity

`QuarterRootTheorem.superquadratic_quarter_root` selects a dimension internally using R=(log N)^(1/4). Its exact finite domain is log N≥8⁴, 2≤T≤N, and T≤N^(2/3)exp(-32(log N)^(3/4)); it returns an actual graph on Fin N with exactly T terminals and E≥T²exp(sqrt(log N)) for every preserving subgraph.

`QuarterRootEventual.superquadratic_quarter_root_eventual` fixes B first, chooses one N0, then uniformly quantifies every later N and every admissible T. The exp(sqrt(log N)) gain is real and the eventual domain is not empty. The finite threshold 8⁴ alone does not guarantee a T≥2 exists; the audited contract correctly does not say that. The separate nonvacuity check proves the cap admits T=2 for all sufficiently large N, with log N≥64⁴ a sufficient explicit threshold.

This is a corrected theorem. The original square-root-deficit existential has not been proved, but its acceptance as superseded is part of the review contract. The numerical obstructions do not establish its falsehood for arbitrary graphs.

## 7. Auxiliary Theorems 5–6 and Lemma 7

Theorem 5's printed sqrt(1+a²) construction has a precise simple-path counterexample at n=30, ell=3, x=10. The designated cost 2sqrt(82) exceeds 4+2sqrt(37). `WeightedConstruction.designated_not_shortest` proves this symbolically; it is a construction counterexample, not a refutation of the existential theorem. The repaired construction has exact k*n*x edge count, x indexed routes through each vertex, edge ownership, native uniqueness, and distinct route supports when k>0. The baseline must be retained in any public note.

`TheoremSix.exact_arbitrary_layer_size` fixes d≥2 and one K>0 before N,k,x. For N>0, k>0 and ((k+1)K)^(d(d−1))*x^(d+1)≤N^(d−1), it produces actual directions and a graph on Fin(k+1) × (Unit→ZMod N), with exactly N vertices per layer, kNx edges, x incidence, distinct canonical supports, and unique edge ownership. Any competitor of length≤k is the canonical native walk. `exact_layer_directions` proves a carry-free positional encoding at arbitrary exact N; the theorem is not restricted to perfect-power layer sizes. The separately proved planar and d≥3 lattice inputs discharge all geometry. x=0 is explicitly handled. The depth restriction is necessary for an indexed set of distinct paths; one-layer labels would otherwise duplicate the same zero-edge walk.

`ObstacleProduct.Data` only supplies ordinary combinatorial incidence/layer/edge-injection data. The concrete constructions fill it. In the unweighted Lemma 7 proof, outer and inner uniqueness are native walk statements and the layer structure yields shortestness; factorization proves full route uniqueness and actual edge forcing. The weighted generic lemma takes real finite positive edge weights and genuine input outer/inner uniqueness. `exists_path_perturbation` selects one positive epsilon over the finite set of all endpoint-pair simple paths before any particular pair or competitor; positivity then extends uniqueness to arbitrary walks by strict bypass/cycle deletion. The same epsilon forces every output edge. Outer weights are symmetric by construction; symmetric inner weights imply symmetric output weights in `product_weight_symmetric`. The theorem does not claim zero/signed/infinite weighted uniqueness.

## 8. Four additions beyond the previous whole-package audit

- `UnlayeredEnvelope` is a numeric implication under explicit capacity/size/edge-budget inequalities. The polynomial and logarithmic elimination correctly bounds only that idealized count family. The connector term is included in `full_product_sqrt_deficit` with an explicit factor three.
- `NaturalBoundary` gives actual natural-number subsequences N=2^(3q²), T=2^(2q²−kq), eventual admissibility, a real little-o relation and bounded count-template gain. It does not turn a template upper bound into an arbitrary-graph upper bound.
- `ConnectorPacking` proves a metric packing injection into an actual connected unweighted gadget. It uses port-separation inequalities and at least two ports; no unique paths, degree bound or tree hypothesis is hidden. The conclusion is a vertex lower bound for realizing those separations, not a global preserver bound.
- `SharedCopyLift` constructs r² copies and shared connectors from an explicitly supplied input lower bound. Walk projection charges inner distance plus connectors; equality forces a route to remain inside the copy determined by both terminal indices. Copy subgraphs preserve the input distances, including unreachable pairs. Counting disjoint tagged inner edges yields r²m forced edges, r²n+2rs vertices, and 2rs terminals. The assumed lower bound is on the input F, not the constructed output G. This is a genuine transfer theorem but gives no normalized-gain amplification (the terminal-square ratio changes by a constant factor).

All four were included in the full defining-module declaration/type/body traversal, not accepted merely from their prior component reviews.

## 9. Foundational and audit-tool boundaries

The independent audit inventories 2,074 paper declarations in all 116 defining modules (1,743 theorems, 316 definitions, and 15 inductive/constructor/recursor declarations), including private/generated names. It traverses checked types and bodies, not only cached axiom metadata. Its union has 49,287 constants and only propext, Classical.choice and Quot.sound. No unsafe constant occurs.

Three compiler-generated partial auxiliaries occur in the full declaration inventory: `walkOfSequence._unsafe_rec`, `DirectionEncoding.encode._unsafe_rec`, and the new `SharedCopyLift.connectors._unsafe_rec`. None is in any of the 23 mapped root closures. A reverse dependency check goes further: none is in the checked proof closure of any of the 1,743 project theorems. They are computational auxiliaries generated alongside ordinary terminating definitions, not admitted proofs.

Lean's standard replay skips unsafe/partial constants, so CI replay alone is not evidence of their absence. The independent closure driver rejects them before passing a full theorem dependency closure into an empty kernel environment. The standard Lean kernel and the three named foundational axioms remain trusted. Selected fresh local source elaborations supplement exact-commit full CI; this is not a claim to have rebuilt all of mathlib locally or manually reread every imported proof line.

## 10. Nonblocking source-comment finding

Some early module headers still describe already-discharged downstream work as unfinished: `LatticeHull.lean` lines 10–14, `HigherBehrend.lean` lines 5–7, `HigherProduct.lean` lines 5–8, and `PathPerturbation.lean` lines 4–8. The conditional theorem signatures themselves are appropriate reusable helpers, and the final exported theorems discharge their inputs. The accepted scope/statement map is accurate. Recommendation: replace these stale global-status phrases with forward references to the completing modules in a later documentation-only cleanup. This is an underclaim/readability issue, not a mathematical blocker or a reason to amend frozen proof bodies.

## 11. Companion annotation and publication conditions

The local companion candidate is separate from deployment. It preserves all ten original marker placements, all 95 assets, and every HTML byte outside the marker blocks relative to Site source a58a0b96. The three dp-1 notes now include the essential k*x² baseline; dp-6 and dp-7 accurately disclose the helper replacement and leaf/runtime boundary. The authoritative marker-plan JSON matches the actual candidate. Independent reruns of the current DOM harness, all nine diagram tests, and 432 marker interaction groups at widths 320/768/1440 passed. This is DOM/simulated geometry QA, not newly rendered pixel QA.

Before any deployment/completion announcement, refresh the historical verification panel with the final audit scope and exact candidate CI result, preserve original source text and controls, and verify the final live audience/access, readback, fidelity, links and interactions. Public linking/audience changes remain separate owner-authorized actions. This report does not authorize or perform them.

## 12. Exclusions that must remain visible

No certification of every literal original lemma/proof sentence; no sharper binomial total branching count; no false leaf equality; no O(n²) rerouting execution/runtime; no original Euclidean weight assignment; no superseded square-root-deficit existential; no zero/one-terminal positive lower bound; no arbitrary-label one-layer distinct path family; no signed/infinite-weight extension; no newly proved quoted background table or quantitative RS literature estimates; no open question settled; no arbitrary-graph impossibility inferred from restricted obstructions.
