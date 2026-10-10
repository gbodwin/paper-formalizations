# Greedy Algorithms for Shortcut Sets and Hopsets

**Status: the actual unweighted shortcut and nonnegative-weighted hopset greedy algorithms now have checked correctness and the logarithmic Section 2.1 warm-up size bound. Exact finite directed and undirected nonnegative-weight versions of Theorem 1.7 are now locally checked; a parameterized DAG greedy size bound is locally checked; its optimized presentation and the chain theorems remain incomplete.**

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

The DAG potential-progress inequality and parameterized output bound are proved in the latest continuation. Its optimized real-root presentation, Algorithm 2, and the chain-proof repair remain incomplete. The finite directed and undirected statements have separate benchmarks and edge-count conventions. Real-log asymptotic presentation and broader weight-domain conventions remain explicit scope obligations.

- `BenchmarkParameters`: monotonicity of the directed benchmark in vertex/edge/budget parameters, independence from the finite vertex type at equal cardinality, and the explicit sufficient comparison budget `m/(12*Nat.log 2 n)` for n≥2.
- `SymmetricWeights`: reversal of actual weighted shortest walks, symmetric distance/hopdistance, and a symmetric unique-minimum-hop perturbation.
- `UndirectedArcs`, `UndirectedGreedy`, and `UndirectedPotential`: unordered edge choices realized by both directed arcs, each charged once; actual greedy correctness; and proof that the ordered-pair potential equals twice the unordered-pair potential, so it selects the same maximum-drop choices.
- `UndirectedProgress` and `UndirectedBenchmark`: the graph-specific comparison argument and a least universal benchmark restricted to symmetric graphs/weights. With `k=Nat.log 2 (n^3)+1`, `h=m/(4*k)`, and `β=max 1 (2*exopt_undirected(n,2*m,h))`, the actual unordered-edge greedy output has at most m edges, preserves distances, and meets β. Its comparison graphs have at most 2m unordered edges.

The latest undirected extension has passed local compilation, the 516-declaration standard-axiom audit, and kernel replay. Independent semantic review passed for the seven new undirected/parameter modules. Exact-commit CI remains a separate pending check. The checked weighted model currently assumes nonnegative real input weights; arbitrary real weights and negative-cycle conventions are not silently included.

The fourteen-module checkpoint [c87c625c](https://github.com/gbodwin/paper-formalizations/commit/c87c625c4ec61b8a3544f879d113e23680083a65) passed [full repository CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38059800129), including all-declaration audit and independent kernel replay. The newer local results are recorded separately in [the verification record](verification/local-result.json); local checks do not assert that a pending exact-commit CI run has passed.

## Current DAG heavy/light continuation

Eleven new modules connect the counting argument to actual canonical paths and actual greedy states. `SuffixWindowPath` and `CanonicalSuffixPath` construct a short canonical path in G∪H with at most floor(β/8) vertices and `β*φ ≤ 256*n*Σ suffdeg`. `SuffixIncidence` and `SuffixIntersections` identify true suffix-path incidence and prove the heavy intersections are intervals. `CanonicalSavings` proves equal-separation shortcuts yield genuine per-demand hop savings. `HeavyCharging` proves the heavy branch `σ*φ ≤ 512*n*drop`.

`LightReroute` constructs the actual replacement walk through the base path. `PrefixIncidence` selects a shared first-quarter source. `LightCharging` chooses the earliest base-path suffix intersection and proves the light branch `β^3*φ ≤ 16384*σ*n^2*drop`. Neither branch assumes a quantitative progress or shortcut-size conclusion.

`DAGProgress.output_card_bound` applies the dichotomy to every actual greedy state of a DAG. For every integer β≥8 and σ≥8, the actual output size is at most

`(Nat.log 2 (n^3)+1) * max (512*n/σ+1) (16384*σ*n^2/β^3+1)`.

All divisions in this expression are natural-number divisions. This is a parameterized finite theorem, before the optimizing choice of σ and conversion to the paper's real-root presentation. General-directed preprocessing, Algorithm 2 and its chain-proof repair, and runtime interfaces are still open.

The 44-module/686-declaration local gate passed, with all modules independently kernel-replayed and only the three standard axioms. Independent semantic review of these eleven new DAG modules is pending; the full paper remains partially formalized. The preceding directed benchmark checkpoint [bb2f37c8](https://github.com/gbodwin/paper-formalizations/commit/bb2f37c83eeb17ff92b9c22ce7f76b91f0c312aa) passed [full CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38061724072). The newer [33-module CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38062811537) and this latest checkpoint's CI are tracked separately.
