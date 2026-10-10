# Greedy Algorithms for Shortcut Sets and Hopsets

**Status: partial. Actual directed and unordered-edge nonnegative weighted greedy correctness, warm-up bounds, and finite Theorem 1.7 analogues are checked. The optimized DAG size theorem, actual SCC reduction, explicit kernel composition, and actual Algorithm 2 ordinary-hop correctness are checked. The complete general-directed theorem with an explicit fourth-power logarithmic factor and the paper's real-power tradeoff is now checked. An unconditional quadratic-progress theorem now gives a weaker explicit size bound for the actual chain greedy; its logarithm-free refinement is recorded below. Actual four-hop path preprocessing with an exact iterated-logarithmic edge bound is now constructed internally. Cubic moment averaging now improves the unconditional weaker DAG output to an exact integer n^(11/9)-scale bound at n^(1/3)-scale hops, with all choices constructed internally. The chain cubic-progress/near-linear-size theorem remains open. Exact local, independent-review and CI evidence is listed below.**

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

A separate [counterfamily analysis](verification/approximate-heredity-counterfamily.md) rules out even a universal constant-factor hereditary repair on an **exact globally maximum** normalized-minimum path. Its rebased-to-original suffix ratio tends to zero. That earlier family alone does not rule out a near-maximum-pair repair, and does not refute cubic progress: explicit middle-arm edges in the same family give cubic drop. The included ordinary proof and [standard-library checker](verification/verify-stretched-symmetric-obstruction.py), checked through arm length 128, are diagnostic evidence rather than Lean proofs.

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

## Logarithm-free quadratic-derived chain bound

`FiniteQuadraticDecay` proves an integer reciprocal-decay estimate: if a monotone natural potential satisfies `P_i^2 ≤ K (P_i-P_(i+1))`, then `(i+1) P_i ≤ K`. Combining this with an active-step floor `D^2 ≤ 25 (P_i-P_(i+1))` proves exact stopping after `2*(25*S/D+1)` steps when `K=25*S^2` and `D>0`.

`ChainQuadraticSharp` supplies both inequalities for the actual raw-potential chain greedy from the proved quadratic shortcut progress. The clipped potential is only proof bookkeeping; neither the selected edges nor the original stopping predicate changes. For every `D≥3`, the actual greedy-stage output has at most

`2*(25*(n*I)/D+1)`

edges, with natural-number division. The same literal preprocessing-plus-greedy output has size at most `K*n+2*(25*(n*I)/D+1)`. At the supplied cover scale `I≤2*r^2`, uncovered-path bound `r`, and target `D=r≥3`, it has at most `K*n+100*n*r+2` edges and ordinary hopbound `7*r+4`.

Thus the previously proved weaker `O(n^(4/3) log n)` greedy-stage guarantee improves to `O(n^(4/3))` at the paper's scale. The source's cubic progress and linear greedy-stage size remain unresolved. This refinement does not add a caller-supplied quantitative progress premise.

The 92-module/1384-declaration checkpoint passed the local source/root build, all-declaration allowed-axiom audit and independent kernel replays of both new modules, with all prior source hashes unchanged. The two exact-hash source reviews passed: [integer decay](verification/finite-quadratic-decay-semantic-review.json) and [actual graph/output join](verification/chain-quadratic-sharp-semantic-review.json). Exact-commit CI is tracked separately; these local results do not claim a pending CI has passed.


## Internally constructed finite chain cover and weaker output

`UniformChainPacking` selects a maximum-cardinality pairwise-disjoint family of actual reachability chains, each with exactly `r` vertices. Its size times `r` is at most `n`. `PackedChainCover` extracts any `r` selected vertices of an original simple path in their actual path order; maximality then proves that every original path has at most `r-1` uncovered vertices. Thus the finite cover guarantee is constructed rather than supplied by the caller.

`PackedChainOutput` additionally chooses the existing forward-clique path witness internally. For every finite DAG, integer `r≥3` with `n≤r^3`, its same literal full shortcut output is legal, has at most `51*n*r+2` edges and ordinary hopbound `7*r+2`. Its `defaultOutput` chooses the least such radius, so `defaultOutput_spec` has only the finite DAG as input. The least-radius and predecessor-cube facts give an exact integer cube-root-scale formulation, including empty and small graphs.

This closes the finite cover/preprocessing witness obligations for the weaker quadratic-derived output. It does not establish the cited almost-linear cover algorithm, the improved `n log* n` preprocessing cost, cubic raw-potential progress, or the source's linear greedy-stage count. Full-paper status remains partial.

The 95-module/1443-declaration checkpoint passed strict local source/root builds, the allowed-axiom audit and all three new independent kernel replays, with all prior source hashes unchanged. Exact-hash semantic reviews passed for the finite cover construction and the fully internal output. Exact-commit CI is tracked separately. A source-preserving earlier CI-only checkpoint raised the job allowance from 30 to 60 minutes after an older full replay was cancelled at the 30-minute boundary; no proof gate was removed.

Reviews: [finite packing and cover](verification/uniform-chain-cover-semantic-review.json), [internal output and radius](verification/packed-chain-output-semantic-review.json).

## Fixed-source interior replacement and multi-source charging

`ChainInteriorSavings` replaces an interior segment `q` of an actual minimum valid walk by a legal edge, retaining the original source. Its endpoint must be an actual entry for that source. Exact splitting cancels both pivot corrections and proves a real saving of at least `count(q)-2`; no source-rebased optimality is used.

`ChainRectangleCharging` aggregates these savings over a source-target product without double counting. Its structural theorem assumes actual minimum-path factorizations through the shared segment and the correct entry condition for every source. These are explicit structural inputs, not a proved existence theorem for a large rectangle. The general cubic progress and linear greedy-stage bound remain open.

The 97-module/1450-declaration checkpoint passes strict local source/root compilation, the allowed-axiom audit, all module indexes, and both new independent kernel replays. All preceding 95 source hashes are unchanged. Exact-commit CI remains separate. The [92-module logarithm-free checkpoint](https://github.com/gbodwin/paper-formalizations/commit/bb5dfbed830442935c6e83b8aceeecaee39b0a03) has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38080355553).

A separate [active-regime counterfamily](verification/active-chain-counterfamily/near-maximum-obstruction.md) rules out a proposed constant-factor near-maximum hereditary repair even when `L^3>n`. The same explicit family admits a [direct cubic-saving rectangle](verification/active-chain-counterfamily/cubic-rectangle.md), with raw drop at least `L^3/1152`. Both statements have ordinary mathematical source review and independent finite diagnostics; neither is represented as a Lean theorem. They identify an obstruction to one proof route and an off-path source-multiplicity mechanism, not a refutation or completion of the main theorem.

The two new modules also pass [exact-hash semantic review](verification/chain-interior-rectangle-semantic-review.json).

## Constructed off-path supply from a guard

`ChainGuardSeparation` proves that a valid original-source path to a guard inaccessible from an original-path pivot can share only chains already seen in the prefix ending at that pivot. The common earliest entry would otherwise give a forbidden original reachability path from the pivot to the guard.

Consequently, a minimum guard path uses at least `distance(s,z)-count(prefix)` chains absent from the original path. A concrete finite set of distinct actual important entry vertices witnesses this off-path supply. The existing guard dichotomy constructs such a guard and minimum path from a strict triangle failure. Distinctness is proved within one supply set; no distinctness of different guards or minimum-path incidence for the new vertices as rebased sources is asserted.

The 98-module/1460-declaration checkpoint passes strict source/root compilation, the allowed-axiom audit and an independent kernel replay of the new module; all prior source hashes are unchanged. The module also passes [exact-source semantic review](verification/chain-guard-separation-semantic-review.json). Exact-commit CI remains separate.

A separately labeled [collision family](verification/active-chain-counterfamily/guard-collisions.md) shows that quadratically many strict rebasing failures can yield the same constructive last-bad-edge guard, even in the active regime. Its ordinary proof and six independent finite checks also exhibit a cubic-saving off-path edge in that family. General cubic progress and the linear greedy-stage bound remain open.

## Fixed-source cone depletion

`ChainGuardCone` defines the actual set of source-valid chain entries that can reach a target. These sets nest under original reachability. Every chain visited by a valid path belongs to the target cone. An inaccessible guard excludes all chains that occur after the original prefix, yielding the exact bound `cone(s,z).card + count(P) ≤ cone(s,t).card + count(prefix)`. This is additive depletion within the unchanged source filter; it supplies no multiplicative shrink or distinctness between arbitrary guards.

The 99-module/1469-declaration checkpoint passes strict local source/root compilation, the allowed-axiom audit, all module indexes and the new independent kernel replay. Prior 98 module hashes are unchanged, and the new module passes [exact-source semantic review](verification/chain-guard-cone-semantic-review.json). The [97-module checkpoint](https://github.com/gbodwin/paper-formalizations/commit/d325c3bea4bdac247c38a11ca980122fe860861b) has [full successful CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38082689984). New exact-commit CI is tracked separately.

A separate [ordinary additive-window proof](verification/active-chain-counterfamily/additive-guard-window.md) uses nested cone deletion to find an edge with raw drop at least `2*k^3`, where `k=floor(L^2/(64*K))≥1` and `K` is the initial fixed-source cone size. This ordinary proof was independently reviewed; its subsequent Lean formalization is described below. The general cubic progress, linear greedy-stage count, claimed near-linear size and efficient construction bounds remain open.

## Cone-sensitive additive-window progress

Seven new modules formalize the additive-window argument for the actual normalized chain potential. `FiniteGuardDescent` maintains a linear length/rank invariant while each bad state strictly decreases finite cone rank. `ChainGuardWindow` constructs every step from a real cheap end-window and proves the resulting stable target remains important, reaches the original target and retains at least half its initial distance. This does not assume multiplicative cone shrinkage or independent guards.

`ChainEntryLevels`, `ChainWindowRoutes` and `ChainWindowPositions` construct actual important entry positions, prove original-source prefix optimality, and bound the inserted route using validity inheritance alone. `ChainStableRectangle` then constructs k distinct sources and k distinct targets in the stable path. Their old distances are at least 4k, while the same legal edge gives actual new valid routes of cost at most 2k. The original raw potential therefore drops by at least 2k³; no source-rebased minimum-path hypothesis or supplied saving rectangle is used.

Precisely, for any legal current shortcut set H, actual important pair (s,t), positive integers L and k, distance_H(s,t)≥L, and K equal to the actual original fixed-source cone cardinality, `exists_window_drop_for_pair` proves

`64*K*k ≤ L²  ⇒  ∃ legal edge e, 2*k³ ≤ potential(H)-potential(H∪{e})`.

Under the additional regime `128*K ≤ L²`, choosing k=floor(L²/(64K)) gives the exact natural-number consequence

`L⁶ ≤ 1048576*K³*(potential(H)-potential(H∪{e}))`.

`step_window_drop` transfers the constructed saving to the literal raw-potential minimizer whenever its stopping predicate is false. These are cone-sensitive bounds. They do not establish universal cubic progress when K is large relative to L, the paper's linear greedy-stage bound, its claimed near-linear full size, or its fast preprocessing construction. Full-paper status remains partial.

The 106-module/1539-declaration checkpoint passes strict local compilation of all seven new sources, the root import and the allowed-axiom audit. All seven additions were independently kernel-replayed, all five paper module indexes passed, and all 99 prior proof hashes are unchanged. Exact-source semantic reviews cover [guard descent](verification/chain-guard-window-semantic-review.json), [entry and route interfaces](verification/chain-window-routes-semantic-review.json), and [stable rectangle and progress](verification/chain-stable-rectangle-semantic-review.json). The [98-module checkpoint](https://github.com/gbodwin/paper-formalizations/commit/e58ea90ba70949d6c9bc68619b02796b94cd4eef) has [full successful exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38083439070). New exact-commit CI is tracked separately; these local results do not claim a pending run has passed.

## Constructed logarithmic path preprocessing

`PathMedianEdges` defines a concrete balanced-median edge recursion on ordered path vertices. Every edge points strictly forward and stays inside the original vertex interval. At depth d its edge set has at most m*d edges; whenever m≤2^d, every ordered pair has a literal route of at most two edges, with equality legs omitted.

`PathMedianWitness` chooses d=ceil(log₂m) and constructs the actual `PathWitness`: at most m*ceil(log₂m) edges and genuine two-hop routes, including empty and singleton paths. It also instantiates the existing disjoint-chain union without any supplied path-preprocessing theorem. For a family of disjoint chains on n vertices, the constructed union uses at most n*ceil(log₂n) edges and meets the required at-most-four-hop per-chain interface.

This replaces the quadratic forward-clique baseline for the path-witness interface with logarithmic-size preprocessing. The published default DAG output still uses its previously defined clique witness; substituting the new witness into a new complete-output definition is a separate step. The stronger four-hop O(n log* n) construction and any machine-runtime bound remain separate. This preprocessing result does not establish universal cubic progress or the paper's linear greedy-stage bound.

The 108-module/1594-declaration checkpoint passes strict source/root compilation, the allowed-axiom audit, all five paper module indexes and both new independent kernel replays. All 106 preceding source hashes are unchanged. The pair passes [exact-source semantic review](verification/path-median-semantic-review.json). The [99-module checkpoint](https://github.com/gbodwin/paper-formalizations/commit/c1697eeb71cbbbe203197d88e3f103ba439e41ef) has [full successful exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38084512910). Later exact-commit CI remains separate.


## Constructed four-hop iterated-logarithmic preprocessing

The ten `PathFour*`, `PathBlock*`, `PathRouteWitness` and `PathOrderedTwoHop` modules construct a literal directed-path shortcut network. Its edges are strictly forward and stay inside the actual path. Consecutive nonempty blocks use counted entry/exit spokes, a deduplicated ordered endpoint set with an actual two-hop median network, and recursively translated networks on the true block sizes. Singleton endpoints contribute equality legs rather than loops; the last block is never padded with nonexistent vertices.

Define tower(0)=2, tower(d+1)=2^tower(d), and height(m) as the least d with m≤tower(d). `height_zero` proves height(m)=0 for m≤2; `height_clog` proves height(m)=height(ceil(log₂m))+1 for m>2. At depth d, `edges_spec` proves the actual edge set has at most (6d+1)m edges and at most four literal legs for every ordered pair whenever m≤tower(d). `route_walk` converts those same legs into native directed walks. Thus the internally constructed ambient witness uses at most (6·height(n)+1)n edges, with four-hop reachability, giving the exact finite iterated-logarithmic preprocessing bound.

`fourHopPackedOutput` installs this witness in the existing actual chain-greedy output, with the finite chain cover also constructed internally. For each finite DAG and integer r≥3 with n≤r³, its same output is legal, has at most (6·height(r)+1)n+50nr+2 edges, and ordinary hopbound 7r+2. `fourHopDefaultOutput` chooses the previously proved least admissible radius internally. The legacy clique-backed output remains available.

The preprocessing size dependency is now proved. The overall output still uses the weaker quadratic-derived greedy bound: universal cubic chain progress, the paper's linear greedy-stage count and near-linear total size, and efficient cover/physical runtime remain open. This is a partial-paper checkpoint.

The 118-module/1731-declaration checkpoint passes strict local source/root compilation, the standard-axiom audit, all five paper module indexes and independent kernel replays of all ten new modules. All 108 prior source hashes are unchanged. The complete ten-source batch passes [exact-source semantic review](verification/path-four-semantic-review.json). Independent finite diagnostics also checked every ordered pair for path sizes 0 through 128; these diagnostics are supplementary, not a replacement for the proofs. The [106-module additive-window checkpoint](https://github.com/gbodwin/paper-formalizations/commit/dddcd6ebea27861f29980f59320c410e01b72c8a) has [full successful exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38086103955). Later exact-commit CI remains separate.


## Exact endpoint baseline and demand-sensitive greedy bound

`ChainEndpointFloor` proves that every actual walk contains the distinct covered-chain labels of its two endpoints. Their cardinality is an immutable lower floor, at most two, for every reachable normalized distance. A demand already at that floor remains saturated after later insertions. Covered endpoints on different chains attain the exact floor two under direct repair.

`ChainExcessPotential` subtracts only this fixed floor from each important demand. The raw potential equals the fixed floor sum plus the excess sum, so every insertion has exactly the same raw and excess marginal. The set of unsaturated important demands only shrinks. If U is its cardinality at the initial greedy state, after the fixed chain preprocessing, and L is the current largest important distance, the actual excess is at most U·L.

`ChainExcessSharp` applies the existing constructed quadratic progress to this sharper account along the same literal raw-greedy run. For every D≥3, `output_card_unsaturated_sharp` proves that its actual final output contains at most `2*(25*U/D+1)` greedy edges, using natural division. The choice function and maximum-distance stopping test are unchanged; the clipped live excess is used only in the proof. Since U is at most the total number of important demands, this refines the previous quadratic-derived coefficient. It does not establish universal cubic progress or the source's linear greedy-stage bound.

A separately labeled [ordinary padding proof and review](verification/active-chain-counterfamily/uniform-prefix-padding.md) explains why uniform chain size alone cannot provide useful source multiplicity. Fresh prefix vertices can all have permanently saturated rows, while all old distances and raw marginals are preserved. The supplied chains form a maximum uniform packing at the canonical radius. In the explicit active guard-collision family, 3m off-path chains contain 3mr vertices but at most 3m+1 source rows can ever improve. The original cubic-saving edge survives. This is an obstruction to a proposed counting route, not a counterexample to cubic progress, and the graph-padding transformation is not yet a Lean theorem. Its thirteen finite diagnostics are supplementary to the ordinary proof and remain separate from the three Lean modules.

The 121-module/1772-declaration checkpoint passes strict local source/root compilation, the standard-axiom audit, all five paper module indexes and independent kernel replays of all three new modules. All 118 prior source hashes are unchanged. The batch passes [exact-source semantic review](verification/chain-excess-semantic-review.json); its report records the source review before the later strict and replay gates, which have now passed at those exact hashes. The [118-module four-hop checkpoint](https://github.com/gbodwin/paper-formalizations/commit/4901c9bb0397a88b39b313eb3d1a3bf4f6089cbc) has [full successful exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38088524294). The new checkpoint's exact-commit CI is tracked separately.


## Actual unsaturated-source support and a linear regime

`ChainSourceSupport` bounds the actual unsaturated demand count by S·I, where S is the number of initially unsaturated source rows and I is the chain-index count. This gives the unchanged raw-greedy output bound `2*(25*S*I/D+1)`, for D≥3. Under the explicit source-mass premise S·I≤b·n·D, the same output has at most 50bn+2 edges.

The module also gives a concrete original-graph certificate for excluding source rows. If every important demand outside a finite set C is either a self-pair or already an original directed edge, a literal zero- or one-edge valid walk attains its exact endpoint-label floor. Hence S≤|C|. Combining |C|≤bI, I≤D² and n=ID proves the linear bound, with every graph and counting premise visible.

These are finite regime theorems, rather than a universal cubic-progress or near-linear-size result. The separately reviewed uniform-prefix padding construction satisfies this certificate with C the old vertices and bounded old-chain length b, but that graph transformation remains ordinary mathematics outside Lean. Thus the sparse-source padding obstruction already lies in a linear greedy regime; a proof covering arbitrary dense-source instances is still missing.

The 122-module/1788-declaration checkpoint passes strict local source/root compilation, the standard-axiom audit, all five paper module indexes and the new independent kernel replay. All 121 preceding proof hashes are unchanged. The new module passes [exact-source semantic review](verification/chain-source-support-semantic-review.json). Full exact-commit CI for this checkpoint is tracked separately; the most recent verified complete run at publication is the [118-module four-hop checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/38088524294).

## Cubic moment averaging and a sharper unconditional weaker output

`ChainShortcutChoices` constructs k² distinct legal important shortcut edges for every important demand of normalized distance at least 4k. Each edge saves at least 2k on that original demand by replacing its actual middle segment, while keeping the original source filter. The destination remains an earliest entry for the new edge's source by the proved entry-inheritance property. No source-rebased minimum-path claim is used.

`ChainMomentProgress` averages over important non-self pairs, whose cardinality is at most |important|≤nI. Exact raw marginal accounting proves

`Σ_(s,t important) max(distance_H(s,t)−3,0)^3 ≤ 32*|important|*rawStepDrop`.

It also proves the corresponding cubic saving when an explicit fixed fraction of important demands is long. This is a cubic moment average. It is not the missing universal cube of the maximum distance.

`ChainCubicPotential` applies finite power-mean and actual positive raw progress to obtain `potential(H)^3 ≤256*|important|^3*rawStepDrop` at every active state. `FiniteCubicDecay` proves that cubic natural decay becomes the existing quadratic reciprocal decay after squaring the potential. Together with the established active-step floor D²≤25*drop, it yields an exact two-block stopping bound. `ChainMomentSharp` attaches it to the same literal raw-greedy run and maximum-distance stopping rule: for D≥3, R>0 and R³≤D², its output has at most `2*(256*n*I/R²+1)` greedy edges. R is only a numerical scale, not a graph-progress assumption.

`PathMomentPackedOutput` applies this bound to the existing internally constructed four-hop path preprocessing and finite maximum chain packing. For k≥2 and n≤k⁹, the actual output at threshold k³ has at most

`(6*height(k³)+1)*n +512*n*k²+2`

edges and at most `7*k³+2` ordinary hops. `momentDefaultOutput` selects the least such k internally, and proves k⁹≤512n for n>0. This is the exact integer n^(11/9)-scale improvement over the earlier n^(4/3)-scale weaker construction, at the same n^(1/3) hop scale. All cover, preprocessing, choices and stopping bounds are internal; the legacy outputs remain available.

The paper remains partial. Universal maximum-distance cubic progress, linear greedy-stage cardinality and the complete near-linear-size target, efficient maximum-packing construction and physical runtime remain open. The new moment theorem is a different, rigorously weaker route rather than a proof of the disputed hereditary-optimality argument.

The 128-module/1855-declaration checkpoint passes strict local source/root compilation, the standard-axiom audit, all five paper module indexes and all six new independent kernel replays. All 122 prior source hashes are unchanged. The batch passes [exact-hash skeptical semantic review](verification/chain-moment-semantic-review.json), covering the original objective, distinctness and denominator, squared decay, active domains and integer scale choices. The [121-module endpoint-excess checkpoint](https://github.com/gbodwin/paper-formalizations/commit/1afd57c07f4d167244b42d9233a266ac24b94507) has [full successful exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38090389644). Later exact-commit CI is tracked separately.

## Saturation-aware moment averaging

`ChainSaturatedTransport` proves a restricted reverse-validity statement: a route attaining its endpoint-label floor contains only those endpoint labels. If both endpoints are important entries for one original source, its entry selectors agree on both labels, so this route is valid for that original source. A fixed-source entry-distance gap greater than two therefore excludes endpoint saturation. This does not restore general source-rebased minimum-path optimality.

`ChainUnsaturatedChoices` applies this result to the actual first/last entry rectangles. Every one of their k² distinct choices is an unsaturated important pair in the current state. `ChainUnsaturatedMoment` consequently proves the exact all-state raw marginal estimate

`Σ_important max(distance_H(s,t)−3,0)^3 ≤32*U_H*rawStepDrop`,

where U_H is the current number of unsaturated important demands. The algorithm still minimizes the full original raw potential over its original candidates.

`ChainUnsaturatedPotential` applies power mean to the exact endpoint-excess account, obtaining `excess(H)^3 ≤256*U_H^3*rawStepDrop`. Saturation persists, so U_H≤U_initial. `ChainUnsaturatedSharp` combines the same clipped account, exact marginal identity, original stopping rule and numerical cubic-decay theorem. For D≥3, R>0 and R³≤D², the actual final greedy output has at most

`2*(256*U_initial/R²+1)`

edges. The zero-unsaturated-demand case is covered. This strengthens the earlier data-sensitive quadratic bound while leaving the actual greedy run unchanged. It does not improve the worst-case n^(11/9)-scale conclusion without a further structural bound on U_initial; the universal maximum-distance cubic and nearlinear paper target remain open.

The 133-module/1894-declaration checkpoint passes strict local source/root compilation, the standard-axiom audit, all five paper module indexes and all five new independent kernel replays. All 128 preceding proof hashes are unchanged. The batch passes [exact-source semantic review](verification/chain-unsaturated-semantic-review.json). The [122-module source-support checkpoint](https://github.com/gbodwin/paper-formalizations/commit/777882f449d0fc182655094ba0488b1b89bc3446) has [full successful exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38091014877). The [128-module moment checkpoint](https://github.com/gbodwin/paper-formalizations/commit/51da6e76b3ae2605aa7adb782ff7df0a3e2a1f75) has a separate [CI run](https://github.com/gbodwin/paper-formalizations/actions/runs/38092824364). This checkpoint's full CI is also tracked separately; the source review is component-scoped, and the full paper remains partial.
