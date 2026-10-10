# Greedy Algorithms for Shortcut Sets and Hopsets

**Status: partial. Actual directed and unordered-edge nonnegative weighted greedy correctness, warm-up bounds, and finite Theorem 1.7 analogues are checked. The optimized DAG size theorem, actual SCC reduction, explicit kernel composition, and actual Algorithm 2 ordinary-hop correctness are checked. The complete general-directed theorem with an explicit fourth-power logarithmic factor and the paper's real-power tradeoff is now checked. An unconditional quadratic-progress theorem now gives a weaker explicit size bound for the actual chain greedy. The chain cubic-progress/near-linear-size theorem remains open. Exact local, independent-review and CI evidence is listed below.**

Source: [arXiv:2511.20111v2](https://arxiv.org/abs/2511.20111v2), posted 26 April 2026.

The [source map](verification/source-scope.md) distinguishes the paper's original results from cited background and records the planned proof obligations. The [independent review](verification/independent-source-diagnostics.json) confirms two incorrect intermediate proof assertions, with exact finite examples. Neither is a counterexample to a main theorem.

- Section 2.2: the potential and its averaging denominator count different sets of pairs. An exact correction to the explanation of the cited BRR algorithm is recorded; only its rounding/counting arithmetic is formalized so far.
- Lemma 5.7's proof: a normalized-shortest valid path need not have normalized-shortest subpaths, even under the longest-shortest qualifier. The cubic potential-drop conclusion and the main theorem remain unresolved by this diagnostic.

Reproduce the finite diagnostics (Python 3 standard library only):

```sh
cd 'Greedy Algorithms for Shortcut Sets and Hopsets/verification'
python check_source_examples.py
python chain_potential_model.py
```

These executable checks support the source audit; they are not Lean kernel proofs. In particular, the example that refutes the hereditary-optimality step still satisfies the paper's cubic drop inequality in the tested instances.

No companion website has yet been published for this paper.

## Current Lean coverage

- `RecapArithmetic`: exact end offsets, old/new distance-index inequalities, rectangle cardinality and the conditional insertion-count bound for the corrected explanation of the cited BRR rule.
- `FinitePotential`: a monotone natural potential with relative progress halves in an exact integer block, obeys a dyadic bound, and eventually vanishes.
- `FiniteGreedy`: an actual finite minimum-new-potential insertion run, its maximum-drop property, termination, stability after zero potential, and output-cardinality bounds under an explicit relative-progress interface.

- `DirectedPaths`: native directed walks, consistent shortest paths, true minimum hop distance, and preservation of original reachability under closure-edge insertion. The tiebreaking construction imports an already-proved local library theorem.
- `GraphGreedy`: Algorithm 1 instantiated on its actual unweighted graph potential. Strict progress, termination, reachability preservation, final hopbound, the elementary quadratic size bound, and the cubic initial-potential bound are proved. Its sharper DAG relative progress is discharged in the later `DAGProgress` module.
- `ShortcutWalk`: replaces an actual path segment by an added directed edge. For an active demand of length greater than β≥4, constructs exactly (⌊β/4⌋+1)² distinct legal edges, each of which reduces that demand to at most β hops.

- `FiniteCharging`: rigorous finite double counting of individual demand repairs, and the exact integer relative-progress denominator.
- `WarmupUnweighted`: the warm-up size bound for the actual unweighted greedy output, with no graph-progress premise left open. For β≥4 its size is at most `(Nat.log 2 (n^3) + 1) * (n^2 / (β/4 + 1)^2 + 1)`, with natural-number divisions.

- `WarmupBound`: the explicit rounded bound `(Nat.log 2 (n^3) + 1) * (16*n^2/β^2 + 1)` for every integer β≥1, including the small-target case.
- `CanonicalSegments`: real native path segments and the DAG-only order-convex intersection property for consistent canonical paths.
- `FiniteWindows`: exact truncated-window multiplicities, incidence double counting and Cauchy–Schwarz averaging. Its actual suffix-family application is supplied by `SuffixWindowPath` and `CanonicalSuffixPath`.

- `WeightedPaths` and `WeightedPerturbation`: the finite nonnegative-real-weight version of Lemma 4.2. One actual positive reweighting simultaneously gives unique shortest walks that are original minimum-hop shortest paths. Uniqueness ranges over all native allowed walks, with cycle erasure explicitly proved.
- `WeightedHopDistance`: actual minimum-hop weighted distance and insertion-sensitive closure weights, with exact distance preservation. Original weights change to closure distances only on inserted pairs.

- `WeightedMonotonicity` and `WeightedGreedy`: actual weighted Algorithm 1, monotone minimum-hop shortest distances, legal insertion, exact distance preservation, termination and final hopbound.
- `WeightedShortcut` and `WarmupWeighted`: shortest-preserving replacement of native subwalks, full demand-rectangle double counting, and the same explicit logarithmic warm-up bound for every integer β≥1.
- `FamilyWindows`: exact finite averaging for variable-length path families; its suffix-path graph instantiation is proved in the later DAG continuation.
- `FiniteHorizon`: a stopping-time/cardinality bridge that requires relative progress only before the specified round budget, for the first-m-round use in Theorem 1.7.

- `WeightedExpansion`, `WeightedSavings`, and `WeightedProgress`: the intended multi-hopedge savings inequality of Lemma 4.3, proved by native shortest-path expansion and finite averaging. See the [corrected exposition](verification/lemma-4-3-correction.md) for the paper's display/indexing repairs.
- `WeightedTransfer` and `WeightedStateProgress`: transfer from a compatible unique-shortest perturbation back to the actual insertion-sensitive greedy state.
- `WeightedBenchmark`: a least universal benchmark over every graph with at most n vertices and m ordered edges, and the exact finite directed nonnegative-weight near-existential output theorem. With `k=Nat.log 2 (n^3)+1`, `h=m/(2*k)`, and `β=max 1 (2*exopt(n,2*m,h))`, the actual output has at most m edges, preserves all distances, and has hopbound β. The proof covers zero/small budgets and only uses progress before the m-round horizon.

The DAG potential-progress inequality and its optimized real-root output bound are proved in the later modules. Algorithm 2 and its chain-proof repair remain separate obligations. The finite directed and undirected statements have separate benchmarks and edge-count conventions. Real-log asymptotic presentation and broader weight-domain conventions remain explicit scope obligations.

- `BenchmarkParameters`: monotonicity of the directed benchmark in vertex/edge/budget parameters, independence from the finite vertex type at equal cardinality, and the explicit sufficient comparison budget `m/(12*Nat.log 2 n)` for n≥2.
- `SymmetricWeights`: reversal of actual weighted shortest walks, symmetric distance/hopdistance, and a symmetric unique-minimum-hop perturbation.
- `UndirectedArcs`, `UndirectedGreedy`, and `UndirectedPotential`: unordered edge choices realized by both directed arcs, each charged once; actual greedy correctness; and proof that the ordered-pair potential equals twice the unordered-pair potential, so it selects the same maximum-drop choices.
- `UndirectedProgress` and `UndirectedBenchmark`: the graph-specific comparison argument and a least universal benchmark restricted to symmetric graphs/weights. With `k=Nat.log 2 (n^3)+1`, `h=m/(4*k)`, and `β=max 1 (2*exopt_undirected(n,2*m,h))`, the actual unordered-edge greedy output has at most m edges, preserves distances, and meets β. Its comparison graphs have at most 2m unordered edges.

The 33-module undirected extension passed local compilation, the 516-declaration standard-axiom audit, independent kernel replay, independent semantic review, and [exact-commit full CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38062811537). The checked weighted model currently assumes nonnegative real input weights; arbitrary real weights and negative-cycle conventions are not silently included.

Historical checkpoint: the fourteen-module checkpoint [c87c625c](https://github.com/gbodwin/paper-formalizations/commit/c87c625c4ec61b8a3544f879d113e23680083a65) passed [full repository CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38059800129), including all-declaration audit and independent kernel replay. The newer local results are recorded separately in [the verification record](verification/local-result.json); local checks do not assert that a pending exact-commit CI run has passed.

## Current DAG heavy/light continuation

Eleven new modules connect the counting argument to actual canonical paths and actual greedy states. `SuffixWindowPath` and `CanonicalSuffixPath` construct a short canonical path in G∪H with at most floor(β/8) vertices and `β*φ ≤ 256*n*Σ suffdeg`. `SuffixIncidence` and `SuffixIntersections` identify true suffix-path incidence and prove the heavy intersections are intervals. `CanonicalSavings` proves equal-separation shortcuts yield genuine per-demand hop savings. `HeavyCharging` proves the heavy branch `σ*φ ≤ 512*n*drop`.

`LightReroute` constructs the actual replacement walk through the base path. `PrefixIncidence` selects a shared first-quarter source. `LightCharging` chooses the earliest base-path suffix intersection and proves the light branch `β^3*φ ≤ 16384*σ*n^2*drop`. Neither branch assumes a quantitative progress or shortcut-size conclusion.

`DAGProgress.output_card_bound` applies the dichotomy to every actual greedy state of a DAG. For every integer β≥8 and σ≥8, the actual output size is at most

`(Nat.log 2 (n^3)+1) * max (512*n/σ+1) (16384*σ*n^2/β^3+1)`.

All divisions in this expression are natural-number divisions. This intermediate parameterized theorem is optimized in `DAGBalance` below. General-directed preprocessing, Algorithm 2 and its chain-proof repair, and runtime interfaces are still open.

The 44-module/686-declaration checkpoint passed local compilation, the standard-axiom audit, all kernel replays, independent semantic review, and [full exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38064334071).

## Optimized DAG theorem

`DAGBalance` chooses `σ = ceil(sqrt(β^3/n)) + 8`, bounds both integer denominators, handles β<8 separately, and converts the square-root ratio to real 3/2 powers. For n≥2 and every integer 1≤β≤n, the actual greedy output satisfies

`|H| ≤ 4*log₂(n) * (16385*n^(3/2)/β^(3/2) + 147456*n^2/β^3)`.

This discharges the DAG part of Theorem 1.4 with an explicit logarithmic factor and absolute constants. The additional general-directed preprocessing statement remains separate, as do the chain theorem and runtime interfaces. The previous parameterized-bound section is a historical intermediate checkpoint.

The optimized 45-module/705-declaration checkpoint passed local compilation, the standard-axiom audit, all kernel replays, both [graph-specific](verification/dag-heavy-light-semantic-review.json) and [balancing](verification/dag-balance-semantic-review.json) independent semantic reviews, and [full exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38065003352).

## Chain preprocessing and valid-walk foundations

`DirectedMap` maps native directed walks along injective chain embeddings. `ChainUnion` constructs the disjoint-chain union, proves reachability preservation and the `K*n` size bound, and gives four-hop paths for forward ordered pairs. The prior path super-shortcut theorem is exposed as a finite `PathWitness m K` input; this checkpoint proves its chain-family application rather than silently treating the entire corollary as an assumption. The interface is nonvacuous, with a proved quadratic forward-clique witness; the cited result supplies the improved logarithmic-iteration factor.

`ChainFirst` constructs unique chain labels and actual earliest reachable chain entries. `NormalizedReachability` proves earliest-entry filtering preserves reachable pairs, using a strict ancestor-count induction in the DAG. `NormalizedValidity` proves every chain visit is contiguous. `ChainNormalization` supplies these hypotheses from the constructed chain union, establishing that the paper's valid walks really exist. None of these proofs asserts hereditary optimality of the normalized shortest paths; the Lemma 5.7 repair and cubic progress bound remain open.

`DAGAllTargets` additionally proves that the actual greedy output is empty for β≥n, extending the source-shaped DAG bound to every positive integer β when n≥2.

The 52-module/803-declaration local audit and kernel gate passed, and the [independent seven-module semantic review](verification/chain-foundations-semantic-review.json) passed with all source hashes bound to commit [9fb851a5](https://github.com/gbodwin/paper-formalizations/commit/9fb851a5c04dda83d83e6ef45a71cf7e6c8edfb6). Its [exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38066160806) passed. Full-paper status remains partial; a fresh end-to-end skeptical audit is required before any eventual completion claim.

## Actual chain Algorithm 2

`ChainDistance` minimizes the number of visited chains over actual source-dependent earliest-entry filtered walks. The minimum exists by the proved reachability construction and decreases under edge insertion. `ChainImportantPairs` constructs the actual source/earliest-entry demand set with at most `n*ℓ` pairs, proves the raw potential bound `n*ℓ²`, and proves strict graph-specific progress whenever the target D≥2 is violated: the direct repair of a violating important pair is a legal closure edge and reduces its normalized distance to at most two.

`FiniteThresholdGreedy` implements a raw-potential minimizer with a separate monotone stopping predicate. This distinction matters: Algorithm 2's raw distance sum need not be zero at termination. `ChainGreedy` instantiates that exact algorithm, proves finite termination and legality, and obtains real normalized walks of cost at most D for every important pair. The greedy-stage bound is `n²`; the complete preprocessing-plus-greedy shortcut set is explicitly constructed, preserves exactly the original reachability, and has the elementary bound `K*n+n²`. The sharper cubic progress rate, claimed near-linear final size, chain-cover hop conversion, and general-directed preprocessing remain open.

`ChainValidity` verifies that legal states remain acyclic, every allowed walk is simple, and all normalized minimizers have contiguous chain visits. It does not assume or claim hereditary normalized optimality.

The 57-module/925-declaration aggregate local gate passed, including all standard-axiom checks and all five new independent kernel replays. The preceding 52 sources are hash-identical to their checked checkpoint. The [independent semantic review](verification/algorithm2-semantic-review.json) of these five additions passed with exact source hashes. The [57-module exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38067616177) passed.

## Actual SCC preprocessing and DAG-greedy application

`DirectedLift` substitutes actual bounded original walks into a contracted walk. `SCCQuotient` constructs the mutual-reachability quotient and representatives, proves the original-edge condensation acyclic, and proves exact reachability equivalence. `SCCStars` constructs the two-way representative stars with at most `2*n` legal edges and expands each condensation edge to at most three actual hops.

`SCCGreedy` runs the verified DAG greedy algorithm on that actual condensation and lifts its selected edges. Its output preserves reachability, has hopbound `3*β+2`, and has size at most `2*n+F(q,β)`, where q is the actual number of components and F is the checked explicit logarithmic DAG bound. The q≤1 case is proved separately. For an exact target B≥5, choosing β=floor((B−2)/3) gives hopbound at most B.

This completes the explicit SCC application in the first bullet of Section 3.3. The source relation can contain diagonal component edges, which are harmless under the already documented loop-insensitive native walk model. The small-budget sampling kernel and the final all-regime general-directed asymptotic conversion remain open; no executable SCC runtime is claimed.

All 61 modules passed local compilation, the 973-declaration standard-axiom audit, and independent kernel replay. The [independent four-module SCC semantic review](verification/scc-preprocessing-semantic-review.json) passed with exact source hashes. The preceding [57-module checkpoint](https://github.com/gbodwin/paper-formalizations/commit/e2567147fc7c95ab8a0919a217aca442ae16edaf) has a separate [CI run](https://github.com/gbodwin/paper-formalizations/actions/runs/38067616177). This latest exact-commit CI remains pending; the full paper remains partial.

## Explicit kernel composition interface

`KernelLift` specifies an injective smaller-graph embedding, actual original walks of length at most L for every kernel edge, and access walks of length at most R from original demands to reachable kernel pairs (or an already-short original path). It then maps the actual SCC/DAG greedy output back to the original graph, proving legality, exact reachability preservation, no increase in edge count, and hopbound `2*R+L*(3*β+2)`. The identity kernel is constructed, proving this interface nonvacuous.

This is a conditional application of an explicit kernel certificate, not a proof that a kernel with an improved vertex count exists. The cited small-kernel existence theorem and its optimized all-regime parameter substitution remain open obligations. The interface contains no greedy progress or shortcut-size conclusion.

The 62-module/1006-declaration local audit and all independent kernel replays passed. The [independent kernel-composition review](verification/kernel-lift-semantic-review.json) passed with the exact source hash. New exact-commit CI remains separate; full-paper status is still partial.

## Validity under changing the source

`ChainSubwalk` proves that an earliest-entry walk valid relative to an ancestor source remains valid when rebased to its own starting vertex. It consequently proves that every subwalk of a valid path is itself valid. The proof uses the constructed selectors, original reachability, and legal augmentations; it makes no shortestness assertion. The 63-module/1009-declaration aggregate local audit passed, the new module was independently kernel-replayed, and its [source-bound semantic review](verification/chain-subwalk-semantic-review.json) passed.

A [ten-vertex counterexample](verification/existential-hereditary-max-path-counterexample.md), with an [independent exhaustive checker](verification/verify-symmetric-existential-counterexample.py), also rules out our proposed weaker repair that *some* globally maximum normalized-shortest path is hereditarily shortest. This is a counterexample to that proposed repair route. It does not refute the claimed cubic progress inequality or the main shortcut theorem. The route is closed; a direct charging argument or another repair is still needed.

The previous 62-module kernel-interface checkpoint is [30667894](https://github.com/gbodwin/paper-formalizations/commit/306678949d8cef4a11d24bdecda95227bd477bd6), with its own [CI run](https://github.com/gbodwin/paper-formalizations/actions/runs/38068839706). The strongest completed full CI at this documentation checkpoint is the 57-module result linked above. Full-paper status remains partial.

## Ordinary-hop correctness from the chain cover

`ChainCover` proves that any legally augmented walk expands to an original directed walk retaining every old vertex. Since the original graph is acyclic, the expanded walk is a simple path, so the original cover's uncovered-vertex budget U still applies. It also extracts a last covered vertex with an original suffix of at most U hops and constructs actual same-chain walks of at most four hops. The cited cover's existence is represented by the explicit `IsCover T U` premise.

`ColoredHopBound` compresses a supplied walk by taking an ordinary shortest path in a fixed graph restricted to the supplied walk's colors and uncovered vertices. Each color contributes at most five vertices, because a longer span admits an actual four-hop replacement in that same fixed graph. This ordinary shortest-path argument does not use source-rebased normalized optimality. `ChainHopCompression` consequently obtains an actual path of at most `U+5*d'(s,t)` hops.

`ChainHopCorrectness.shortcuts_hop_bound` applies these facts to the actual Algorithm 2 output: for every original reachable pair, its output has a real path of at most `2*U+5*D+4` hops whenever the normalized stopping target is D≥2. This closes the ordinary-hop correctness bridge. The claimed cubic progress, near-linear shortcut count, and geometric phase analysis remain open.

The 67-module/1043-declaration local root and allowed-axiom audit passed, all four new modules were independently kernel-replayed, and the [exact-hash four-module semantic review](verification/chain-hop-semantic-review.json) passed. All preceding 63 proof hashes are unchanged. The strongest completed full CI at this checkpoint is the [62-module kernel-interface commit](https://github.com/gbodwin/paper-formalizations/commit/306678949d8cef4a11d24bdecda95227bd477bd6), with [successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38068839706). Later exact-commit CI is tracked separately. The full paper remains partial.

## Finite kernel balancing and target rounding

`KernelBalance` applies the actual DAG progress theorem with σ=8 inside the actual SCC kernel construction. If the supplied kernel has M≤b³ vertices and b≥8, its selected edge count is at most `(Nat.log 2 (M^3)+1)*(131074*M+1)`. When the access budget R≤L, its external hopbound is at most `7*L*b`, hence the hopbound times b² is at most 7Z if `L*b³≤Z`.

`KernelTarget` chooses `b=max(8, Nat.sqrt(7*Z/B)+1)` for a positive requested target B. It proves the actual output meets B under that explicit scale condition, and bounds its size by `(Nat.log 2 (b^9)+1)*(131074*b^3+1)`. The square-root integer division and all positivity hypotheses are proved. These are finite applications of the supplied geometric kernel certificate. Kernel existence with this smaller cardinality and scale remains an explicit cited-background obligation; no unconditional all-regime result is claimed.

The 69-module/1068-declaration local gate passed, both new modules were independently kernel-replayed, and the [exact-hash semantic review](verification/kernel-balance-target-semantic-review.json) passed. All earlier 67 source hashes are unchanged. The strongest completed full CI at this checkpoint is [1557b325](https://github.com/gbodwin/paper-formalizations/commit/1557b32516892fbf67074c8cec9be2325abc2d9a), with [successful 63-module CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38069588019). The 67-module ordinary-hop checkpoint [4dc9122f](https://github.com/gbodwin/paper-formalizations/commit/4dc9122f9844e4831d93bb052f8dd562fb026e05) has a separate [CI run](https://github.com/gbodwin/paper-formalizations/actions/runs/38070529386). Full-paper status remains partial.

## Unconditional low-target general-directed bound

`SCCBudget` absorbs the actual representative-star overhead when the inner target b satisfies `b³≤n`. The actual SCC/DAG output then has `|H|*b³ ≤ 264000*(Nat.log 2 (n³)+1)*n²`. For B≥5, the exact choice `b=floor((B−2)/3)` meets the requested hopbound and gives `|H|*B³ ≤ 90552000*(Nat.log 2 (n³)+1)*n²` in that explicit regime. Targets 1≤B<5 use the actual original greedy output and satisfy `|H|*B³≤64*n²`. No small-kernel certificate is assumed for this low-target result.

The 70-module/1084-declaration local gate and new independent kernel replay passed, as did the [exact-source semantic review](verification/scc-budget-semantic-review.json). The [67-module ordinary-hop checkpoint](https://github.com/gbodwin/paper-formalizations/commit/4dc9122f9844e4831d93bb052f8dd562fb026e05) now has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38070529386). Later exact-commit CI remains separate. The high-target kernel existence/scale and chain cubic progress remain open; full-paper status remains partial.

## A proved ingredient for the remaining chain argument

`ChainCounting` proves exact visited-chain accounting for spliced native walks. `ChainGuard` examines the last edge of a rebased walk incompatible with an ancestor source's earliest-entry rule. A minimum u-to-t walk either gives the actual triangle bound `d′(s,t)≤d′(s,u)+d′(u,t)`, or yields an earlier important target z, unreachable from u, satisfying `d′(s,t)+1≤d′(s,z)+d′(u,t)`. The proof uses a genuine within-chain splice and counts its shared endpoint once.

This is a proved ingredient, not the missing cubic progress theorem: possible repeated charges to the same guard still need a multiplicity argument. All 72 modules passed the local root gate and 1102-declaration audit; both new modules were independently kernel-replayed and passed [source-bound semantic review](verification/chain-guard-semantic-review.json). The preceding [70-module SCC-bound checkpoint](https://github.com/gbodwin/paper-formalizations/commit/065c50beb2ef413b5fe139b759bf079c654e11ad) has its separate [CI run](https://github.com/gbodwin/paper-formalizations/actions/runs/38072349779). Full-paper status remains partial.

## Constructed deterministic small kernel

`FiniteHitting` constructs an actual maximum-coverage greedy hitting set by applying proved incidence counting and the finite potential-halving theorem. `KernelSamples` applies it to consistently selected shortest paths. Every long canonical interval is hit, giving a smaller graph whose vertices are the selected vertices and whose edges represent original paths of at most r+1 hops. The actual `sampleKernel` supplies all geometric fields: access at most 2r, edge expansion at most 2r+2, and at most `(Nat.log 2 (n²)+1)*(n/(r+1)+1)` sampled vertices. It applies to every finite directed graph, including r=0. No external kernel-existence premise or DAG assumption is used.

This construction supersedes the earlier geometric-existence boundary. The optimized high-target numerical range split and final all-regime size presentation are still open. The construction is noncomputable finite greedy, so it does not establish implementation runtime. The chain cubic-progress gap also remains open.

All 74 modules passed the local root gate and 1161-declaration allowed-axiom audit. Both additions were independently kernel-replayed and passed [exact-source semantic review](verification/sample-kernel-semantic-review.json). The strongest completed exact-commit CI is the [69-module checkpoint](https://github.com/gbodwin/paper-formalizations/commit/6f6af0ac72f9a1705178f549a44f4411765acf6c), with [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38071444030). Later checkpoint CI remains separate. Full-paper status remains partial.

## Concrete all-regime general-directed construction

`KernelSamplingBalance` selects the deterministic hitting radius `floor(2*k*n/b³)`, where `k=Nat.log 2 (n²)+1`, and proves its actual sample count and lifting scale. `KernelRegimes` exhaustively classifies a rounded target parameter that fails this scale: either n is bounded by a polynomial in k, or the ordinary SCC overhead is absorbed by the cubic term. `SCCGeneral` proves the needed unconditioned SCC bound, retaining all rounding losses.

`GeneralDirected.output` constructs the complete finite output for every B≥1. It returns no edges for B≥n, uses original greedy for the remaining B<5 cases, uses the concrete sampled-kernel greedy when balanced, and otherwise uses the actual SCC/DAG fallback. `output_hop` proves the requested hopbound B, and `output_card` proves the explicit finite `bound n B` displayed in that module. Its hypotheses contain no kernel witness, progress assumption, size conclusion, or numerical regime restriction. The bound has a log/root kernel term, a pure polylogarithmic term, and a logarithmic multiple of `n²/B³+1`. The simpler source-style real-power conversion remains separate.

All 78 modules passed local compilation and the 1237-declaration allowed-axiom audit. All four additions were independently kernel-replayed and passed [exact-source semantic review](verification/general-directed-semantic-review.json). The strongest completed exact-commit CI is [065c50be](https://github.com/gbodwin/paper-formalizations/commit/065c50beb2ef413b5fe139b759bf079c654e11ad), with [successful 70-module CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38072349779). Later CI remains separate. This does not resolve the chain cubic-progress claim; full-paper status remains partial.


## Explicit general-directed real-power theorem

`GeneralIntegerBound` bounds the rounded kernel parameter, its logarithm, and the finite fallback terms by a single fourth power of `k=Nat.log 2 (n²)+1`. `GeneralPowerBound.output_card_log` then proves, for every finite directed graph with n≥2 vertices and every integer B≥1,

`|GeneralDirected.output G B| ≤ 1152000000000000000 * log₂(n)^4 * (n^(3/2)/B^(3/2) + n²/B³)`.

The same actual output preserves exactly the original reachability and has hopbound B, by `GeneralDirected.output_legal` and `output_hop`. Targets B≥n use the proved empty-output branch. All floor and square-root losses and the conversion to real 3/2 powers are included. This closes the source-shaped general-directed part of Theorem 1.4; it does not assert that the unmodified original greedy algorithm alone achieves this bound on arbitrary directed graphs.

All 80 indexed modules passed the local root gate and the 1267-declaration allowed-axiom audit. Both arithmetic additions were independently kernel-replayed. The preceding 78 source hashes are unchanged. The [exact-source arithmetic review](verification/general-power-semantic-review.json) passed. Exact-commit CI remains separate. The strongest completed CI at this checkpoint is [737a2040](https://github.com/gbodwin/paper-formalizations/commit/737a204016dbb7108f5e55dc36833780756bc780), with [successful 74-module CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38073791373).

The chain cubic-progress/near-linear-size proof, the cited cover-construction interfaces, and runtime scope remain separate. Full-paper status remains partial, and no companion Site is published.


## Exact fixed-source chain prefixes and entries

`ChainPrefix` proves that the chain sets on either side of a valid path split intersect exactly in the pivot's chain label, giving exact cost additivity with zero correction for an uncovered pivot. This proves that a prefix of a normalized minimum path is minimum when its original source is retained. It does not assert the disproved source-rebased subpath property.

`ChainEntries` proves that every visited chain's earliest original-source entry is on that same actual path. These entries are distinct, are actual important targets, and their number is the path's chain count. Each prefix ending at such a target has chain count equal to its actual old normalized distance. These are concrete ingredients for direct charging; no cubic progress or multiplicity bound is claimed.

All 82 indexed modules passed the local root gate and the 1286-declaration allowed-axiom audit. Both additions were independently kernel-replayed and passed [prefix](verification/chain-prefix-semantic-review.json) and [entry](verification/chain-entries-semantic-review.json) exact-source semantic reviews. The preceding eighty source hashes are unchanged. The [80-module real-power checkpoint](https://github.com/gbodwin/paper-formalizations/commit/84b907010804099edc0bbe1a380cdf3d5dbe6689) has its separate [CI run](https://github.com/gbodwin/paper-formalizations/actions/runs/38075526807). Full-paper status remains partial.


## Concrete one-source chain charging

`ChainPrefixSavings` proves that inserting the actual important prefix pair (s,u) saves at least k−2 on every appropriate original-source minimum prefix extension. The original covered pivot cancels exactly; the unchanged suffix remains allowed. A prefix count of at least two also proves the pair is a genuine non-self closure edge.

`ChainSuffixCharging` constructs at least L−k distinct actual important targets on the suffix and aggregates each one's k−2 saving exactly once in the original raw potential. Thus the literal insertion has potential drop at least `(L−k)*(k−2)`, with no rebased optimality, progress premise, or caller-supplied target set. Selecting an attained middle level and obtaining enough additional distinct sources for cubic progress remain separate obligations.

All 84 indexed modules passed the local root gate and the 1300-declaration allowed-axiom audit. Both additions were independently kernel-replayed and passed [exact-source review](verification/chain-suffix-charging-semantic-review.json); the preceding 82 source hashes are unchanged. The [80-module real-power checkpoint](https://github.com/gbodwin/paper-formalizations/commit/84b907010804099edc0bbe1a380cdf3d5dbe6689) now has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38075526807). Later exact-commit CI remains separate. Full-paper status remains partial.

A separate [counterfamily analysis](verification/approximate-heredity-counterfamily.md) rules out even a universal constant-factor hereditary repair on an **exact globally maximum** normalized-minimum path. Its rebased-to-original suffix ratio tends to zero. This does not rule out a near-maximum-pair repair, and does not refute cubic progress: explicit middle-arm edges in the same family give cubic drop. The included ordinary proof and [standard-library checker](verification/verify-stretched-symmetric-obstruction.py), checked through arm length 128, are diagnostic evidence rather than Lean proofs.

## Unconditional quadratic progress and a weaker Algorithm 2 size theorem

`ChainLevels` proves that every intermediate noninitial integer chain-count level is attained at an actual important entry on the same valid path. `ChainQuadraticProgress` applies the preceding one-source charging theorem at a middle level: every important pair at normalized distance L≥4 constructs a legal edge with `L² ≤ 25 * rawPotentialDrop`. No source-rebased optimality or progress oracle is assumed.

`FiniteThresholdDecay` proves a quantitative stopping bound for the unchanged raw-potential minimizer. A potential clipped to zero after stopping is used only as proof bookkeeping; the algorithm still selects by its original raw sum. `ChainRelativeProgress` chooses an actual maximum-distance important pair and establishes the required relative rate for that very greedy step.

`ChainQuadraticSize` proves `ChainDistance.Context.output_card_quadratic`. For every D≥3, the actual Algorithm 2 output satisfies

`|output D| ≤ (Nat.log 2 (n * I²) + 1) * (25 * n * I / D + 1)`,

where n is the number of vertices, I is the number of chains, and division is natural-number division. `Nat.log` includes its zero-input convention, so the finite theorem also covers empty types. The existing legality, reachability, and ordinary-hop correctness theorems apply to the same output. The context still carries its explicit chain family and path-preprocessing witnesses; the cited cover-construction implementation remains a separate interface. At the paper's I=O(n^(2/3)), D=Θ(n^(1/3)) scales, this is O(n^(4/3) log n) for the greedy stage. It is a proved weaker bound, not the claimed linear greedy-stage count or a replacement for the unresolved cubic-progress argument.

All 89 indexed modules passed the local root gate and the 1348-declaration allowed-axiom audit. All five additions were independently kernel-replayed and passed [exact-source semantic review](verification/chain-quadratic-semantic-review.json); the preceding 84 source hashes are unchanged. The [82-module prefix/entry checkpoint](https://github.com/gbodwin/paper-formalizations/commit/024257aaecbe7de149b8e5efd63a6a40a73e8adc) has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38076148756). Later exact-commit CI remains separate. Full-paper status remains partial.

## Full-output finite corollary

`ChainQuadraticOutput` combines the actual preprocessing union with the checked greedy output. The same literal shortcut set is legal, has size at most

`K*n + (Nat.log 2 (n*I²)+1)*(25*n*I/D+1)`,

and has ordinary hopbound `2*U+5*D+4` whenever the supplied chain cover leaves at most U uncovered vertices on a path. At the integer scale `I≤2r²`, `U=D=r≥3`, the bound becomes

`K*n + (Nat.log 2 (n*I²)+1)*(50*n*r+1)`, with at most `7r+4` ordinary hops.

The cited chain-cover and path-preprocessing construction interfaces remain explicit. This is a complete finite size/correctness conjunction for the existing output, with the weaker quadratic-derived size term; cubic progress and the source's linear greedy-stage bound remain unresolved.

All 90 indexed modules passed the local root gate and the 1356-declaration allowed-axiom audit. The new wrapper was independently kernel-replayed and passed [exact-source review](verification/chain-quadratic-output-semantic-review.json); all preceding 89 source hashes are unchanged. The [84-module one-source checkpoint](https://github.com/gbodwin/paper-formalizations/commit/d26b4194dc9eb20f0c85c137981c31123cac6ba2) now has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38077029287). Later exact-commit CI remains separate. Full-paper status remains partial.
