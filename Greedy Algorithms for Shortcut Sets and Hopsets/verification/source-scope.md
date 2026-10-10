# Source-reading checkpoint: Greedy Algorithms for Shortcut Sets and Hopsets

Source: arXiv:2511.20111v2, 26 April 2026. PDF: https://arxiv.org/pdf/2511.20111v2. HTML: https://arxiv.org/html/2511.20111v2.

This is a reading and proof-planning checkpoint, not a completed Lean verification. No original theorem in this paper has yet been declared verified.

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
