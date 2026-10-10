# Source-reading checkpoint: Greedy Algorithms for Shortcut Sets and Hopsets

Source: arXiv:2511.20111v2, 26 April 2026. PDF: https://arxiv.org/pdf/2511.20111v2. HTML: https://arxiv.org/html/2511.20111v2.

This is a partial verification with a chronological proof log, not a completed full-paper verification. Current checked scope includes actual directed greedy correctness, the Section 2.1 warm-up bounds, and the nonnegative-weight version of Lemma 4.2. Exact finite directed and undirected nonnegative-weight Theorem 1.7 analogues are now locally checked. The actual DAG heavy/light dichotomy and parameterized output-size theorem are now locally checked. The optimized DAG real-power/logarithm bound is now locally checked. General-directed preprocessing, chain results, and the remaining domain/runtime presentation are incomplete.

## Source identity

- PDF SHA256: `575ab719d984ec662119e7c83d7a5639be99a370568d298a0113a41a812bade0`
- TeX archive SHA256: `3a237087017a5fab68308532c13c977c36083070278b43bf4d50c9e0ad0be4b9`
- Queue order: 4, after Simple Length-Constrained Expander Decompositions, from the 9 October 2026 publication-order snapshot.

## Original-result obligations

1. Algorithm 1: actual finite greedy choice maximizing the thresholded sum of hopdistances, termination, validity of every inserted closure edge, and final hopbound.
2. Theorem 1.4: DAG shortcut size, with logarithmic factor explicit; instantiate the cited general-directed-graph preprocessing separately. Do not silently claim the unmodified greedy algorithm handles arbitrary directed graphs with the same proof.
3. Lemmas 3.1–3.4: finite canonical consistent shortest paths, suffix-window averaging, heavy/light intersections, exact rounding, potential decrease.
4. Theorem 1.7: exact distance-preserving weighted hopsets, directed and undirected settings, a precise finite definition of exopt, parameter monotonicity, small/zero budget cases, and actual greedy output size at most m.
5. Lemmas 4.1–4.3: unique shortest-path perturbation retaining hop-minimal original shortest paths; bound aggregate savings by the sum of individual empty-hopset savings; compare reweighted and original potential drops.
6. Theorems 1.5/5.1 and Lemma 5.7: actual modified chain-cover greedy algorithm, valid paths and normalized distance, potential phases, conversion back to ordinary hopbound, O(n) greedy edges plus imported O(n log* n) path-super-shortcut edges.
7. Corollary 5.3: combine disjoint chain shortcuts and their size/correctness. Lemma 5.6 composes cited algorithms; clarify whether its implementation and computational model are imported or formalized. Do not label wall-clock runtime proved merely from combinatorial counts.

## Background that can be explicitly imported

- Prior lower bounds and comparisons in the introduction and appendix.
- Theorem 2.1 is explicitly said not to be a new theorem, but its adaptation to this exact potential/greedy rule should be proved as part of the algorithm infrastructure, rather than assumed from a different algorithm.
- Lemma 5.2: Raskhodnikova's path super-shortcut bound and algorithm.
- Cited chain-cover construction components (Kogan–Parter, Cáceres, deterministic min-cost flow) and their runtime interfaces.
- SCC and small-budget kernel reductions cited in Section 3.3; prove their application to the new DAG theorem, not the cited papers from scratch.

## Precise issues to resolve before formal claims

### Section 2.2, printed page 5 / PDF page 7: averaging denominator

The recap defines φ using pairs with hopdistance > β/2, then p using pairs with hopdistance > β, and claims a distance at least φ/p. These two indexing sets differ.

For the directed path on n=2k+3 vertices, empty H, β=2k (k≥1):

- p=3;
- φ = sum(d*(2k+3-d), d=k+1,...,2k+2) = 2(k+1)(k+2)(k+3)/3;
- maximum hopdistance = 2k+2;
- (φ/p)/(maximum hopdistance) = (k+2)(k+3)/9, which grows without bound.

Thus neither a sufficiently-large-β convention nor a hidden absolute constant explains the literal assertion. Counting p over the same threshold β/2 repairs the averaging line only. It does not automatically repair the last claim about p decreasing each round. The paper distinguishes its exact greedy rule from the cited BRR algorithm, so the new theorem is not refuted by this failed recap line. Independent source review confirmed this diagnostic.

### Lemma 5.7 proof, printed page 13 / PDF page 15: hereditary optimality

The sentence that any subpath of a d′-shortest valid path is also d′-shortest needs a separate proof or corrected formulation. A finite diagnostic under the written definition is:

- DAG edges: 0→1→2→3→9; 0→4→5→6→7→8→9; 1→8.
- Chains: {7,8} and singleton chains for all other vertices. They cover every vertex, are disjoint, and there are 9 ≤ 2·10^(2/3) chains. The sole nontrivial chain already has diameter one.
- A minimum-cost valid path from 0 to 9 is (0,1,2,3,9), touching 5 chains. The only competing valid branch touches 6 chains.
- Its subpath (1,2,3,9) touches 4 chains, whereas the valid path (1,8,9) touches 3.
- The full splice (0,1,8,9) is invalid: the earliest vertex of chain {7,8} reachable from 0 is 7. From 1, the earliest reachable vertex is 8.

Both endpoint pairs are important pairs because {9} is a singleton chain. This is a counterexample to the stated intermediate hereditary-optimality assertion, not a counterexample to the asymptotic main theorem or to the full potential-reduction conclusion. Independent source review confirmed this diagnostic. No repair is claimed yet.

### Other proof transcription issues and scope questions

- Lemma 3.2's short canonical path is constructed in the current augmented graph G∪H; the statement says G. The displayed sum has a u/v index mismatch. The Cauchy–Schwarz line should be an inequality rather than a general equality. These appear locally repairable.
- Section 3.1's balanced potential display omits the φ factor, restored in the combined bound later.
- Lemma 4.3's telescoping display reverses the sign of each decrement, and later summands need the condition that the shortcut endpoints occur on the relevant unique path. The intuitive savings inequality admits a direct disjoint-interval proof; the displayed equations should not be copied literally.
- Nonnegative edge weights / existence of shortest paths, integer budget floors, n≤1, m=0, empty active sets, and integer chain-cover rounding need explicit treatment.

## Proof design candidates

- Finite simple directed paths and nonnegative real weights; distinguish reachability from absent/unreachable distance values.
- A general finite greedy potential framework with exact cardinality, contraction phases, and eventual zero potential.
- Deterministic finite perturbations: preserve primary weight, then hop count, then an injective edge-subset tiebreaker. Prove an actual real-weight realization for the exopt application.
- For unique shortest paths, expand every hopedge into a contiguous interval of the original path. Disjoint intervals give a direct upper bound on multi-edge savings by the sum of one-edge savings.
- Keep background algorithms as named, explicit interfaces, and discharge all new graph-specific obligations rather than assuming their conclusions.

## Repair route for the Section 2.2 recap

The primary BRR source, Theorem 5.1 (printed page 434), uses a different edge-selection rule: pick a pair whose current distance exceeds the target and connect two vertices near the two ends of a shortest path. It counts pairs crossing a half-target distance threshold. It does not use the mismatched φ/p average or claim that maximizing the sum potential necessarily maximizes pair elimination. Source: https://drops.dagstuhl.de/storage/00lipics/lipics-vol008-fsttcs2010/LIPIcs.FSTTCS.2010.424/LIPIcs.FSTTCS.2010.424.pdf .

An exact rounded variant, derived here: for integer β≥8, choose a hop-minimal shortest path x₀,…,x_L with L>β. Set r=⌊(β−2)/4⌋ and add the closure edge (x_r,x_(L−r)). For each i∈[0,r] and j∈[L−r,L], the old hopdistance j−i exceeds β/2, while the route using the new edge has at most 2r+1≤β/2 hops. There are (r+1)²≥β²/64 distinct such pairs. The number of reachable pairs whose hopdistance exceeds β/2 never increases; hence this rule uses at most 64n²/β² insertions before all hopdistances are at most β. For weighted exact hopsets, the same argument uses optimal subpaths of a hop-minimal shortest path and distance-closure edge weights.

This repairs the explanation of the cited algorithm without claiming a log-free bound for the current paper's sum-potential-maximizing rule. The separately given Section 2.1 proof remains the route to its stated logarithmic warm-up bound. The exact rounded argument above is a mathematical derivation awaiting Lean formalization, not yet a kernel-checked theorem.

Independent source review of both diagnostics completed on 10 October 2026; evidence is in `independent-source-diagnostics.json`. The chain diagnostic also satisfies the globally-longest-shortest qualifier: max over S of d′ is 5.

## State-model design constraints

The hopset state must retain original weights on original edges unless that ordered pair is explicitly added as a distance-closure edge. An existing input edge can be heavier than the shortest distance between its endpoints; replacing every original edge's weight by the closure distance for free would change the exact greedy algorithm. A faithful finite model can use an allowed-edge predicate E ∪ H and the state-dependent weight w_H(u,v)=dist_G(u,v) on H, original w(u,v) otherwise. This also handles an inserted hopedge parallel to an existing, heavier edge. Shortcut-set states instead use unit weights throughout and need not preserve original distances.

Reachability is fixed across allowed augmentations, but shortest hopdistances are not. The graph-specific layer must prove those facts before instantiating the generic potential theorem. Empty active sets, no candidates, self-pairs, zero-weight cycles, and min-hop optimal path existence require explicit treatment.

The preliminary `FinitePotential.lean` component uses natural-valued monotone potentials. If P(i) ≤ D·(P(i)−P(i+1)) at every step and D>0, it derives 2·P(D)≤P(0), then 2^k·P(kD)≤P(0), and zero potential once 2^k>P(0). This is a conditional arithmetic component, not the paper's graph-specific progress lemma. It compiled and passed all-declaration axiom audit and sequential kernel replay on 10 October 2026, together with `RecapArithmetic`; 22 declarations were audited across the two modules.


## Generic greedy implementation checkpoint

`FiniteGreedy` now defines the actual finite insertion sequence using an argmin of the next natural-valued potential. It proves the maximum-drop characterization, fresh insertion while potential is positive, termination after at most the candidate count, stability after termination, and the dyadic stopping-time/cardinality bound for that actual run. The existence of an improving candidate and the quantitative relative-progress hypothesis remain explicit interfaces. No graph-specific potential reduction is assumed silently or claimed proved.

The three-module checkpoint passed local compilation, all 80 defining-module declarations' standard-axiom audit, and sequential kernel replay on 10 October 2026. Full exact-commit repository CI is a separate check.


## Actual unweighted graph checkpoint

`DirectedPaths` and `GraphGreedy` now discharge the generic strict-progress interface for the exact unweighted directed-graph potential. They prove legal closure-edge insertion, consistent actual shortest paths, unchanged reachability, monotone hop distances, termination and final target hopbound. The initial potential is at most n³ and the elementary output size is at most n². The quantitative relative-progress estimate remains open, rather than being built into the graph model.

`ShortcutWalk` constructs a real allowed replacement walk. For every active path of length L>β≥4, the first ⌊β/4⌋+1 vertices crossed with the last ⌊β/4⌋+1 vertices give exactly (⌊β/4⌋+1)² distinct legal shortcut edges. Each reduces that demand's new hopdistance to at most β. The demand-wise witnesses are combined by the subsequent `FiniteCharging` and `WarmupUnweighted` modules.

This unweighted model does not yet formalize weighted hopsets, the strong DAG size theorem, or Algorithm 2. It also does not claim a computational runtime from its noncomputable finite choice operation.


## Unweighted warm-up bound

`WarmupUnweighted.output_card_bound` now proves the exact finite logarithmic size bound for the actual unweighted Algorithm 1 output, for β≥4. The proof constructs the demand repair rectangles, double counts their contribution to single-edge potential drops, chooses a maximum-drop edge, and invokes the proved finite greedy stopping-time theorem. No quantitative progress assumption remains in this theorem. Its explicit bound is `(Nat.log 2 (n^3) + 1) * (n^2 / (β/4 + 1)^2 + 1)`, using integer division.

This is the unweighted shortcut special case of the Section 2.1 warm-up. It is not a claim to have proved its weighted-hopset version, Theorem 1.4's stronger bound, or the chain algorithm. Eight modules and 188 declarations have passed local compilation, standard-axiom audit and kernel replay; exact-commit CI is tracked separately.


## DAG/window prerequisites and all-positive warm-up targets

`WarmupBound.output_card_bound_all` extends the explicit rounded unweighted bound to every integer β≥1. `CanonicalSegments` proves that consistently selected shortest paths in an acyclic directed graph have order-convex intersections, using actual native segments and directed reachability antisymmetry. `FiniteWindows` proves exact window coverage and finite incidence averaging; the construction of the suffix-family graph witness and the heavy/light potential argument remain separate obligations.

This checkpoint has eleven indexed proof modules and 257 standard-axiom-audited declarations, all locally compiled and kernel-replayed. The preceding eight-module commit 669fd3ac has passed full repository CI. No weighted or main-theorem completion is claimed.


## Weighted foundations checkpoint

`WeightedPerturbation.exists_unique_minhop_reweighting` proves the finite nonnegative-real-weight version of Lemma 4.2. Two actual finite perturbations, first by hop count and then by an injective edge code, produce one positive edge weighting for all reachable pairs. The unique shortest walk is an original minimum-hop shortest path. Positivity and cycle erasure extend uniqueness from simple paths to all native allowed walks.

`WeightedHopDistance` defines actual weighted distance and minimum-hop distance, then proves exact distance preservation under insertion-sensitive closure weights. A hopedge parallel to a heavier original edge changes that pair's weight only when inserted; no free closure-weight replacement is made.

All fourteen indexed modules and 322 defining-module declarations passed local compilation, standard-axiom audit and kernel replay. The main weighted greedy output-size theorem remains incomplete. The paper's introductory definition says only “weighted”; the present formal model explicitly uses nonnegative input weights, including zero weights. Extending or justifying that convention remains a scope obligation before full-paper completion.


## Current weighted greedy and warm-up checkpoint

The earlier checkpoint sections are chronological records. They are superseded on weighted correctness and the warm-up bound by `WeightedGreedy`, `WeightedShortcut`, and `WarmupWeighted`. These now prove the actual directed nonnegative-real-weight greedy output's correctness, exact weighted-distance preservation, and the rounded Section 2.1 size bound `(Nat.log 2 (n^3) + 1) * (16*n^2/β^2 + 1)` for every integer β≥1. Every replacement walk is proved shortest, and the quantitative graph-progress premise is discharged by demand-rectangle double counting.

`FiniteHorizon` supplies the needed bounded-round stopping theorem, with progress required only before the given cardinality budget. `FamilyWindows` handles exact averaging for variable-length path families. Neither silently assumes the still-open main graph-specific progress estimates.

Remaining original-result scope: strong DAG suffix/heavy/light bounds and general-directed reduction arithmetic; the multi-hopedge unique-shortest-path savings lemma and its perturbation transfer; the extremal benchmark and exact budget instantiation; undirected weighted/budget translation; weight-domain scope; Algorithm 2 and repair of Lemma 5.7; claimed runtime interfaces. The paper is still partially formalized.


## Current finite directed near-existential theorem

`WeightedExpansion` and `WeightedSavings` prove the original unique-path multi-edge savings inequality directly, retaining every hopedge's contiguous expansion. `WeightedProgress` derives an individual drop from a comparison hopset of half the target hopbound. `WeightedTransfer` and `WeightedStateProgress` rigorously transfer this to the original weights and current greedy state. The repaired formulas are in [the Lemma 4.3 correction](lemma-4-3-correction.md).

`WeightedBenchmark` defines the least universal hopbound over all finite vertex types with cardinality at most n, all directed relations with at most m ordered edges, and all nonnegative real weights. It proves the actual Algorithm 1 output has size at most m at target `max 1 (2*exopt(n,2*m,h))`, where `h=m/(2*(Nat.log 2 (n^3)+1))`. The initial cubic potential bound, first-m-round graph-size budget, h=0 case, exact distance preservation and output hopbound are all discharged. No quantitative progress premise remains in this theorem.

This is an exact finite directed nonnegative-weight counterpart of Theorem 1.7. Conversion to the paper's real-log asymptotic constant, undirected edge counting/greedy choice and the weight-domain convention remain explicit obligations. The strong DAG and chain theorems are still unfinished. Earlier checkpoint sections above are historical records, superseded where stated here.


## Current unordered-edge undirected theorem

The undirected extension is now locally proved. `UndirectedGreedy` chooses and charges actual unordered edges, and `UndirectedPotential` proves that its ordered-pair objective is exactly twice the unordered-pair objective. `SymmetricWeights` preserves symmetric weights through the unique-shortest perturbation. `UndirectedProgress` gets a 1/(4h) relative drop from a comparison hopset with h unordered edges; no directed edge count is silently substituted.

`UndirectedBenchmark` quantifies over all symmetric NNReal-weighted graphs on at most n vertices with at most m unordered input edges. Its least-bound existence is proved using the empty hopset. At `h=m/(4*(Nat.log 2 (n^3)+1))` and target `max 1 (2*exopt_undirected(n,2*m,h))`, the actual greedy output has at most m unordered edges and the required hopbound and exact distances. Zero budgets and the first-m-round stopping horizon are handled explicitly.

`BenchmarkParameters` also establishes the directed benchmark's parameter monotonicity and cardinality invariance, and an explicit sufficient comparison budget `m/(12*Nat.log 2 n)` for n≥2. The full source's real-log formulation and broader weight-domain conventions remain separate from these exact finite statements. Strong DAG and chain results are still unfinished.

The 33-module, 516-declaration local gate passed; the seven new undirected/parameter modules passed an independent hash-bound semantic review. Exact-commit CI is tracked separately.


## Actual current-graph suffix averaging

`CanonicalSuffixPath.exists_current_high_score_path` now instantiates the finite window averaging with actual active canonical paths and the actual GraphGreedy potential. Its short path is proved optimal in G∪H, correcting the original statement's G notation. The finite inequality is `β*φ ≤ 256*n*Σ suffdeg` and the path has at most floor(β/8) vertices, for β≥8. The 35-module/555-declaration local gate passed; independent review of these two continuation modules is not yet complete. Heavy/light progress and the strong DAG size theorem remain open.


## Actual DAG heavy/light and parameterized size theorem

This section supersedes earlier historical statements that the suffix-family instantiation and heavy/light progress are open. The latest eleven modules prove the exact current-graph suffix-window witness, path-incidence identification, contiguous canonical intersections, real shortcut savings, common-prefix rerouting, and both branches of the original potential argument. The base path is explicitly in G∪H. Integer rounding uses β≥8, σ≥8 and at most floor(β/8) base vertices.

`DAGProgress.local_dichotomy` finds an actual closure edge with either `σ*φ ≤ 512*n*drop` or `β^3*φ ≤ 16384*σ*n^2*drop`. `DAGProgress.output_card_bound` proves the actual maximum-drop greedy output has at most `(Nat.log 2 (n^3)+1) * max (512*n/σ+1) (16384*σ*n^2/β^3+1)` edges, with natural divisions. Quantitative graph progress is proved rather than assumed. The optimizing integer choice, real-root/asymptotic conversion, and cited general-directed preprocessing application remain distinct obligations.

All 44 modules and 686 declarations passed local compilation, allowed-axiom audit and independent kernel replay. The eleven DAG continuation modules await independent semantic review; exact-commit CI is separate. Full-paper status remains partial because Algorithm 2, the Lemma 5.7 repair, remaining parameter/domain issues and runtime interfaces are unfinished.


## Optimized real-power DAG bound

`DAGBalance.output_card_log_bound` proves the original DAG-shaped bound with no asymptotic convention left implicit in its numeric inequality: for n≥2 and 1≤β≤n, the actual output size is at most `4*log₂(n)*(16385*n^(3/2)/β^(3/2)+147456*n^2/β^3)`. The integer choice `ceil(sqrt(β^3/n))+8`, division rounding, small positive targets, real-power identity and logarithm comparison are all proved. Earlier statements that this balancing remains open are historical.

The forty-five-module, 705-declaration local gate passed; all modules were independently kernel-replayed. The eleven-module graph-specific semantic review passed and is included in this checkpoint; the single balancing module also passed independent semantic review. The general-directed SCC/kernel application and Algorithm 2 remain open, and no executable runtime follows from the noncomputable finite choices.


## Chain preprocessing and validity foundation

The finite `PathWitness` interface in `ChainUnion` states the forward path result imported from Raskhodnikova: forward edges on m ordered vertices, at most K*m edges including the original consecutive edges, and actual forward walks of at most four hops. The smaller K remains cited background. Mapping these witnesses to each actual chain and taking their union is proved, with at most K*n edges for vertex-disjoint chains and no loss or creation of original reachability. The corrected Corollary 5.3 qualification is in [the direction note](chain-direction-correction.md).

The concrete chain labels and earliest entries are then constructed. Source-dependent earliest-entry filtering preserves reachability and guarantees contiguous chain visits; actual valid walks exist after the chain union. These results do not assume or repair the incorrect hereditary-optimality assertion. The normalized shortest-distance progress lemma, actual Algorithm 2 analysis and final chain-size theorem remain open.

A separate all-target wrapper proves the DAG greedy output is empty for β≥n, so the real-power/logarithm DAG bound covers every positive integer target. All 52 modules and 803 declarations passed local compilation, standard-axiom audit and kernel replay. Independent semantic review of the seven new foundation/all-target modules is pending; exact-commit CI remains separate.

### Actual Algorithm 2 continuation

The normalized distance is now a minimum over constructed earliest-entry filtered walks, with an explicitly finite value for every original reachable pair. The actual important-pair set is constructed from each source and earliest reachable chain entry; its size is at most n times the number of chains. The potential is the paper's untruncated raw sum, and the stopping predicate is separately the maximum-demand distance target. The finite greedy framework and graph-specific direct repair prove actual Algorithm 2 correctness and termination for every integer target D≥2. No cubic progress premise is smuggled into this result: the currently proved elementary size bound is n². The claimed near-linear chain size theorem still requires a repair of Lemma 5.7, the chain-cover hop conversion and phase arithmetic. All full-paper and final-audit statuses remain partial.

### Actual SCC reduction application

The first Section 3.3 reduction is now constructed directly: actual mutual-reachability quotient, representatives, original-edge condensation, at most2n legal representative stars, three-hop expansion per condensed edge, and the checked DAG greedy output lifted back to G. The result gives size2n+F(q,β) and hopbound3β+2, with exact integer retargeting and a separate q≤1 case. The small-budget sampling kernel and the final all-regime asymptotic parameter conversion remain open. This is a combinatorial construction/correctness theorem, not an executable SCC runtime verification.
