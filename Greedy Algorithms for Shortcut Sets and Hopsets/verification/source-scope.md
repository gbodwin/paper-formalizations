# Source-reading checkpoint: Greedy Algorithms for Shortcut Sets and Hopsets

Source: arXiv:2511.20111v2, 26 April 2026. PDF: https://arxiv.org/pdf/2511.20111v2. HTML: https://arxiv.org/html/2511.20111v2.

This is a partial verification with a chronological proof log. The current checked scope is summarized in the README and `local-result.json`; older checkpoint sections below are historical. Actual Algorithm 1 and its nonnegative weighted directed/undirected finite benchmark bounds, the optimized DAG theorem, the SCC application, explicit kernel composition, and Algorithm 2's ordinary-hop correctness are now proved. The deterministic kernel, complete numerical regime split, and explicit log⁴(n) real-power general-directed theorem are now proved. The chain cubic-progress/near-linear cardinality proof remains open. A fresh skeptical end-to-end audit is required before any eventual completion claim.

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

### Explicit small-kernel application interface

KernelLift proves actual composition of a supplied bounded-walk kernel certificate, SCC preprocessing and DAG greedy. It constructs an identity certificate and derives edge legality, reachability equivalence, image-cardinality bounds and hopbound2R+L(3β+2). Improved-size kernel existence and quantitative parameter optimization are not discharged by this conditional application. No new-paper size or progress conclusion appears in the certificate fields.


### Current ordinary-hop conversion

The four modules `ChainCover`, `ColoredHopBound`, `ChainHopCompression`, and `ChainHopCorrectness` close the previously listed chain-cover-to-hopbound obligation. From the explicit cover budget U, the actual Algorithm 2 output with normalized stopping target D≥2 has ordinary hopbound `2*U+5*D+4` for every original reachable pair. The proof compresses an ordinary shortest path in a fixed color-restricted graph and never invokes the false normalized hereditary-optimality assertion. All four modules passed local compilation, aggregate allowed-axiom audit, independent kernel replay and source-bound reciprocal semantic review. Cubic progress and the sharp cardinality/phase argument remain open.

### Small-kernel background boundary

The cited background is [Bodwin–Hoppenworth, Lemma 13 and its proof](https://arxiv.org/html/2304.02193v2). Its sampling proof constructs at most n/x vertices, access distances at most 4x log n, and kernel edges expandable in at most 8x log n original hops, for the stated asymptotic sampling regime. Integer rounding and small n must be made explicit when supplying that certificate. `KernelLift.Kernel` exposes these geometric properties as finite inputs; the SCC/DAG algorithm, its output, and its composition are proved locally. No new-paper size or potential-progress conclusion is included in the certificate.

The explicit runtime statements in this paper occur in the cited path-super-shortcut lemma, its chain-union corollary, and the composition of cited chain-cover construction algorithms (Lemmas 5.2/5.6 and Corollary 5.3). They are separate background/implementation interfaces. The proof scripts do not establish machine runtime from noncomputable finite choices, and no total greedy machine-runtime theorem is claimed here.


### Conditional balanced kernel application

`KernelBalance` and `KernelTarget` now prove the source-shaped finite parameter calculation for the actual supplied-kernel/SCC/DAG output: near-linear kernel edge count at inner target b when M≤b³, external hopbound at most7Lb, and a rounded square-root parameter meeting a requested target B whenever the explicit scale Lb³≤Z holds. Both modules passed compilation, the aggregate 1068-declaration audit, independent kernel replay and exact-hash semantic review. The smaller certificate's existence and scale, including the range in which the rounded parameter fits the cited sampling theorem, are still assumptions to discharge or import with precise quantifiers. This is not an unconditional all-regime theorem.

### Unconditional low-target SCC absorption

`SCCBudget` proves the general-directed `n²/B³`-shaped bound without a kernel premise when `floor((B−2)/3)³≤n` and B≥5, and separately covers B=1,2,3,4. The proof absorbs the actual 2n representative-star cost, proves the rounded target comparison B≤7b, and retains all constants in a division-free scaled inequality. Its aggregate local audit and independent source review passed. The complementary high-target branch still needs the precise improved-kernel existence/scale application.

### Valid earlier-target guard

The source-rebasing obstruction now has a formal quantitative alternative: a failed triangle comparison produces an actual earlier important target with almost the same ancestor-source distance and no reachability from the intermediate source. The proof selects the last incompatible edge, uses only already-proved validity and chain-set identities, and constructs the splice. This replaces no main theorem yet; controlling repeated guards and deriving cubic potential progress remain open.

### Geometric kernel existence is now constructed

The new deterministic hitting-set proof supersedes the earlier statement that geometric small-kernel existence is only a cited input. For every finite directed graph and integer r≥0, `KernelSamples.sampleKernel` constructs a genuine kernel on at most `(Nat.log 2 (n²)+1)*(n/(r+1)+1)` vertices, with access radius 2r and expansion bound 2r+2. The proof hits consistently selected original shortest-path intervals and inductively connects sampled endpoints with actual short kernel edges; no DAG assumption is needed. The explicit log loss is compatible with the paper's soft-O preprocessing role. Complete parameter/range substitution and its final size presentation remain separate obligations, as does implementation runtime.

### The finite general-directed range split is closed

The four concrete application modules eliminate both the external kernel premise and the remaining numerical regime hypothesis from the final finite graph theorem. The actual all-regime output has requested hopbound B and an explicit log/root/division size bound for every positive B. The empty, small-target, balanced-sampling and SCC-fallback branches are exhaustive. A simpler source-style real-power/soft-O conversion remains separate. This uses noncomputable finite choices and makes no new machine-runtime claim. Chain cubic progress and near-linear Algorithm 2 size remain open.


### General-directed source-shaped presentation is now proved

`GeneralIntegerBound` and `GeneralPowerBound` complete the arithmetic conversion of the constructed output to `1.152e18 * log₂(n)^4 * (n^(3/2)/B^(3/2) + n²/B³)` for n≥2 and every integer B≥1. No external kernel-existence, geometric regime, progress, or cardinality premise is assumed by this final result. The B≥n branch has exactly zero added edges. This completes the combinatorial general-directed Theorem 1.4 tradeoff, via explicitly added kernel/SCC preprocessing. The actual original greedy DAG theorem is a distinct output. No new implementation-runtime claim is made. The separate chain cubic progress and near-linear Algorithm 2 size still require a proof repair.


### Fixed-source prefix optimality is valid

The new exact split identity cancels the same pivot-chain correction when a prefix is replaced in the unchanged source-filtered graph. Consequently a minimum path's prefixes, with their original source, are minimum. The actual earliest entry of every visited chain occurs on the same path, and these vertices form a constructed set of distinct important targets with cardinality equal to its chain count. This provides genuine old-distance accounting for a one-source charging argument. It does not restore source-rebased hereditary optimality, supply the missing additional source multiplicity, or prove cubic progress.


## Concrete one-source chain charging

`ChainPrefixSavings` proves that inserting the actual important prefix pair (s,u) saves at least k−2 on every appropriate original-source minimum prefix extension. The original covered pivot cancels exactly; the unchanged suffix remains allowed. A prefix count of at least two also proves the pair is a genuine non-self closure edge.

`ChainSuffixCharging` constructs at least L−k distinct actual important targets on the suffix and aggregates each one's k−2 saving exactly once in the original raw potential. Thus the literal insertion has potential drop at least `(L−k)*(k−2)`, with no rebased optimality, progress premise, or caller-supplied target set. Selecting an attained middle level and obtaining enough additional distinct sources for cubic progress remain separate obligations.

All 84 indexed modules passed the local root gate and the 1300-declaration allowed-axiom audit. Both additions were independently kernel-replayed and passed [exact-source review](chain-suffix-charging-semantic-review.json); the preceding 82 source hashes are unchanged. The [80-module real-power checkpoint](https://github.com/gbodwin/paper-formalizations/commit/84b907010804099edc0bbe1a380cdf3d5dbe6689) now has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38075526807). Later exact-commit CI remains separate. Full-paper status remains partial.

A separate [counterfamily analysis](approximate-heredity-counterfamily.md) rules out even a universal constant-factor hereditary repair on an **exact globally maximum** normalized-minimum path. Its rebased-to-original suffix ratio tends to zero. That earlier family alone does not rule out a near-maximum-pair repair, and does not refute cubic progress: explicit middle-arm edges in the same family give cubic drop. The included ordinary proof and [standard-library checker](verify-stretched-symmetric-obstruction.py), checked through arm length 128, are diagnostic evidence rather than Lean proofs.

## Unconditional quadratic progress and a weaker Algorithm 2 size theorem

`ChainLevels` proves that every intermediate noninitial integer chain-count level is attained at an actual important entry on the same valid path. `ChainQuadraticProgress` applies the preceding one-source charging theorem at a middle level: every important pair at normalized distance L≥4 constructs a legal edge with `L² ≤ 25 * rawPotentialDrop`. No source-rebased optimality or progress oracle is assumed.

`FiniteThresholdDecay` proves a quantitative stopping bound for the unchanged raw-potential minimizer. A potential clipped to zero after stopping is used only as proof bookkeeping; the algorithm still selects by its original raw sum. `ChainRelativeProgress` chooses an actual maximum-distance important pair and establishes the required relative rate for that very greedy step.

`ChainQuadraticSize` proves `ChainDistance.Context.output_card_quadratic`. For every D≥3, the actual Algorithm 2 output satisfies

`|output D| ≤ (Nat.log 2 (n * I²) + 1) * (25 * n * I / D + 1)`,

where n is the number of vertices, I is the number of chains, and division is natural-number division. `Nat.log` includes its zero-input convention, so the finite theorem also covers empty types. The existing legality, reachability, and ordinary-hop correctness theorems apply to the same output. The context still carries its explicit chain family and path-preprocessing witnesses; the cited cover-construction implementation remains a separate interface. At the paper's I=O(n^(2/3)), D=Θ(n^(1/3)) scales, this is O(n^(4/3) log n) for the greedy stage. It is a proved weaker bound, not the claimed linear greedy-stage count or a replacement for the unresolved cubic-progress argument.

All 89 indexed modules passed the local root gate and the 1348-declaration allowed-axiom audit. All five additions were independently kernel-replayed and passed [exact-source semantic review](chain-quadratic-semantic-review.json); the preceding 84 source hashes are unchanged. The [82-module prefix/entry checkpoint](https://github.com/gbodwin/paper-formalizations/commit/024257aaecbe7de149b8e5efd63a6a40a73e8adc) has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38076148756). Later exact-commit CI remains separate. Full-paper status remains partial.

## Full-output finite corollary

`ChainQuadraticOutput` combines the actual preprocessing union with the checked greedy output. The same literal shortcut set is legal, has size at most

`K*n + (Nat.log 2 (n*I²)+1)*(25*n*I/D+1)`,

and has ordinary hopbound `2*U+5*D+4` whenever the supplied chain cover leaves at most U uncovered vertices on a path. At the integer scale `I≤2r²`, `U=D=r≥3`, the bound becomes

`K*n + (Nat.log 2 (n*I²)+1)*(50*n*r+1)`, with at most `7r+4` ordinary hops.

The cited chain-cover and path-preprocessing construction interfaces remain explicit. This is a complete finite size/correctness conjunction for the existing output, with the weaker quadratic-derived size term; cubic progress and the source's linear greedy-stage bound remain unresolved.

All 90 indexed modules passed the local root gate and the 1356-declaration allowed-axiom audit. The new wrapper was independently kernel-replayed and passed [exact-source review](chain-quadratic-output-semantic-review.json); all preceding 89 source hashes are unchanged. The [84-module one-source checkpoint](https://github.com/gbodwin/paper-formalizations/commit/d26b4194dc9eb20f0c85c137981c31123cac6ba2) now has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38077029287). Later exact-commit CI remains separate. Full-paper status remains partial.

## Logarithm-free quadratic-derived chain bound

`FiniteQuadraticDecay` proves an integer reciprocal-decay estimate: if a monotone natural potential satisfies `P_i^2 ≤ K (P_i-P_(i+1))`, then `(i+1) P_i ≤ K`. Combining this with an active-step floor `D^2 ≤ 25 (P_i-P_(i+1))` proves exact stopping after `2*(25*S/D+1)` steps when `K=25*S^2` and `D>0`.

`ChainQuadraticSharp` supplies both inequalities for the actual raw-potential chain greedy from the proved quadratic shortcut progress. The clipped potential is only proof bookkeeping; neither the selected edges nor the original stopping predicate changes. For every `D≥3`, the actual greedy-stage output has at most

`2*(25*(n*I)/D+1)`

edges, with natural-number division. The same literal preprocessing-plus-greedy output has size at most `K*n+2*(25*(n*I)/D+1)`. At the supplied cover scale `I≤2*r^2`, uncovered-path bound `r`, and target `D=r≥3`, it has at most `K*n+100*n*r+2` edges and ordinary hopbound `7*r+4`.

Thus the previously proved weaker `O(n^(4/3) log n)` greedy-stage guarantee improves to `O(n^(4/3))` at the paper's scale. The source's cubic progress and linear greedy-stage size remain unresolved. This refinement does not add a caller-supplied quantitative progress premise.

The 92-module/1384-declaration checkpoint passed the local source/root build, all-declaration allowed-axiom audit and independent kernel replays of both new modules, with all prior source hashes unchanged. The two exact-hash source reviews passed: [integer decay](finite-quadratic-decay-semantic-review.json) and [actual graph/output join](chain-quadratic-sharp-semantic-review.json). Exact-commit CI is tracked separately; these local results do not claim a pending CI has passed.


## Internally constructed finite chain cover and weaker output

`UniformChainPacking` selects a maximum-cardinality pairwise-disjoint family of actual reachability chains, each with exactly `r` vertices. Its size times `r` is at most `n`. `PackedChainCover` extracts any `r` selected vertices of an original simple path in their actual path order; maximality then proves that every original path has at most `r-1` uncovered vertices. Thus the finite cover guarantee is constructed rather than supplied by the caller.

`PackedChainOutput` additionally chooses the existing forward-clique path witness internally. For every finite DAG, integer `r≥3` with `n≤r^3`, its same literal full shortcut output is legal, has at most `51*n*r+2` edges and ordinary hopbound `7*r+2`. Its `defaultOutput` chooses the least such radius, so `defaultOutput_spec` has only the finite DAG as input. The least-radius and predecessor-cube facts give an exact integer cube-root-scale formulation, including empty and small graphs.

This closes the finite cover/preprocessing witness obligations for the weaker quadratic-derived output. It does not establish the cited almost-linear cover algorithm, the improved `n log* n` preprocessing cost, cubic raw-potential progress, or the source's linear greedy-stage count. Full-paper status remains partial.

The 95-module/1443-declaration checkpoint passed strict local source/root builds, the allowed-axiom audit and all three new independent kernel replays, with all prior source hashes unchanged. Exact-hash semantic reviews passed for the finite cover construction and the fully internal output. Exact-commit CI is tracked separately. A source-preserving earlier CI-only checkpoint raised the job allowance from 30 to 60 minutes after an older full replay was cancelled at the 30-minute boundary; no proof gate was removed.

Reviews: [finite packing and cover](uniform-chain-cover-semantic-review.json), [internal output and radius](packed-chain-output-semantic-review.json).

## Fixed-source interior replacement and multi-source charging

`ChainInteriorSavings` replaces an interior segment `q` of an actual minimum valid walk by a legal edge, retaining the original source. Its endpoint must be an actual entry for that source. Exact splitting cancels both pivot corrections and proves a real saving of at least `count(q)-2`; no source-rebased optimality is used.

`ChainRectangleCharging` aggregates these savings over a source-target product without double counting. Its structural theorem assumes actual minimum-path factorizations through the shared segment and the correct entry condition for every source. These are explicit structural inputs, not a proved existence theorem for a large rectangle. The general cubic progress and linear greedy-stage bound remain open.

The 97-module/1450-declaration checkpoint passes strict local source/root compilation, the allowed-axiom audit, all module indexes, and both new independent kernel replays. All preceding 95 source hashes are unchanged. Exact-commit CI remains separate. The [92-module logarithm-free checkpoint](https://github.com/gbodwin/paper-formalizations/commit/bb5dfbed830442935c6e83b8aceeecaee39b0a03) has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38080355553).

A separate [active-regime counterfamily](active-chain-counterfamily/near-maximum-obstruction.md) rules out a proposed constant-factor near-maximum hereditary repair even when `L^3>n`. The same explicit family admits a [direct cubic-saving rectangle](active-chain-counterfamily/cubic-rectangle.md), with raw drop at least `L^3/1152`. Both statements have ordinary mathematical source review and independent finite diagnostics; neither is represented as a Lean theorem. They identify an obstruction to one proof route and an off-path source-multiplicity mechanism, not a refutation or completion of the main theorem.

The two new modules also pass [exact-hash semantic review](chain-interior-rectangle-semantic-review.json).

## Constructed off-path supply from a guard

`ChainGuardSeparation` proves that a valid original-source path to a guard inaccessible from an original-path pivot can share only chains already seen in the prefix ending at that pivot. The common earliest entry would otherwise give a forbidden original reachability path from the pivot to the guard.

Consequently, a minimum guard path uses at least `distance(s,z)-count(prefix)` chains absent from the original path. A concrete finite set of distinct actual important entry vertices witnesses this off-path supply. The existing guard dichotomy constructs such a guard and minimum path from a strict triangle failure. Distinctness is proved within one supply set; no distinctness of different guards or minimum-path incidence for the new vertices as rebased sources is asserted.

The 98-module/1460-declaration checkpoint passes strict source/root compilation, the allowed-axiom audit and an independent kernel replay of the new module; all prior source hashes are unchanged. The module also passes [exact-source semantic review](chain-guard-separation-semantic-review.json). Exact-commit CI remains separate.

A separately labeled [collision family](active-chain-counterfamily/guard-collisions.md) shows that quadratically many strict rebasing failures can yield the same constructive last-bad-edge guard, even in the active regime. Its ordinary proof and six independent finite checks also exhibit a cubic-saving off-path edge in that family. General cubic progress and the linear greedy-stage bound remain open.

## Fixed-source cone depletion

`ChainGuardCone` defines the actual set of source-valid chain entries that can reach a target. These sets nest under original reachability. Every chain visited by a valid path belongs to the target cone. An inaccessible guard excludes all chains that occur after the original prefix, yielding the exact bound `cone(s,z).card + count(P) ≤ cone(s,t).card + count(prefix)`. This is additive depletion within the unchanged source filter; it supplies no multiplicative shrink or distinctness between arbitrary guards.

The 99-module/1469-declaration checkpoint passes strict local source/root compilation, the allowed-axiom audit, all module indexes and the new independent kernel replay. Prior 98 module hashes are unchanged, and the new module passes [exact-source semantic review](verification/chain-guard-cone-semantic-review.json). The [97-module checkpoint](https://github.com/gbodwin/paper-formalizations/commit/d325c3bea4bdac247c38a11ca980122fe860861b) has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38082689984). New exact-commit CI is tracked separately.

A separate [ordinary additive-window proof](verification/active-chain-counterfamily/additive-guard-window.md) uses nested cone deletion to find an edge with raw drop at least `2*k^3`, where `k=floor(L^2/(64*K))≥1` and `K` is the initial fixed-source cone size. The initially ordinary proof is now formalized by the seven guard-window modules described below. The general cubic progress, linear greedy-stage count, claimed near-linear size and efficient construction bounds remain open.


## Subsequent formalized additions

The seven guard-window modules through `ChainWindowProgress` prove the actual cone-sensitive drop `2*k^3` under `64*K*k≤L²`, with K the actual fixed-source cone size. Under the explicit stronger regime `128*K≤L²`, they prove `L^6≤1048576*K^3*drop` and transfer the saving to the actual active raw-potential minimizer. This leaves universal cubic progress open.

`PathMedianEdges` and `PathMedianWitness` construct a literal two-hop directed path network with at most m·ceil(log₂m) edges. The later ten-module four-hop batch builds on this stronger two-leg interface: counted first/last-block spokes, a deduplicated ordered endpoint median network, and recursively shifted networks on actual nonempty blocks yield `(6*d+1)*m` edges whenever m is below the depth-d tower. The exact least tower height satisfies the ceiling-log iteration, giving the finite O(m log* m) preprocessing result with four native hops, including empty and singleton domains.

`PathFourPackedOutput` uses the constructed iterated-logarithmic witness in the actual chain-greedy output. For every finite DAG and r≥3 with n≤r³, it gives legal shortcuts of size at most `(6*height(r)+1)*n+50*n*r+2` and ordinary hopbound `7*r+2`; its default chooses the least radius internally. This discharges the path-preprocessing size/correctness dependency without an imported path oracle. The separate cited efficient cover/runtime construction, universal cubic chain progress, linear greedy-stage cardinality and near-linear full-output bound remain open. The legacy clique-backed output remains available.

The ten-source [semantic review](path-four-semantic-review.json) is tied to exact hashes. Compiler/audit/replay evidence is recorded in `local-result.json`; full exact-commit repository CI is tracked separately. A fresh independent skeptical end-to-end audit is still required before any eventual whole-paper completion claim.
