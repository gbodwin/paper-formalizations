# Light Edge Fault Tolerant Graph Spanners

Greg Bodwin, Michael Dinitz, Ama Koranteng, and Lily Wang.
Source: [arXiv:2502.10890v2](https://arxiv.org/abs/2502.10890v2), 25 April 2025; ICALP 2025.

**Active partial formalization. The main upper bounds, lower bounds, and polynomial-time theorem are not yet verified.**

## Contracts and mathematical scope

- Finite undirected simple graphs, arbitrary finite edge fault sets, and real edge weights. Walk-based spanner semantics covers disconnected input graphs. Weighted distance is supplied by the already checked LightSpanners library.
- Greedy correctness assumes nonnegative edge weights and stretch at least one. Positivity on actual graph edges and positive denominator are separate hypotheses for lightness results.
- Fault budgets are natural numbers. A real budget is interpreted by its floor; the higher competition parameter uses `2*f + floor(eta*f)` and requires `floor(eta*f)+1` host votes.
- The source extends upper bounds to multigraphs. This extension remains open and will not be inferred from a simple-graph result.
- Asymptotic constants, integer-rounding requirements, small parameter cases, and the base preserver weight must remain explicit. Neither a final inequality nor a packing theorem is hidden in a definition of the construction.

## Checked component modules

- `Basic`: actual edge deletion; EFT spanner and connectivity definitions; edgewise-to-walk stretch; fault-budget monotonicity; every missing input edge has endpoints connected under every allowed preserver fault set.
- `SeededGreedy`: actual recursive construction with an arbitrary seed, preservation of seed edges, no extra edges, coverage, Theorem 18, and equivalence of all-fault tests to current-edge-fault tests.
- `ConnectivityOptimum`: existence and uniqueness of the minimum preserver weight; monotonicity in the fault budget; choice-independent competitive lightness.
- `BlockerSampling`: exact finite Bernoulli pair probabilities and a union-bound survival estimate proving the corrected `1/(2f)` sampling rule including `f=1`; consistent estimator thresholds.

Additional checkpoint components:
- `MetricSemantics`: literal all-pairs ENNReal weighted-distance equivalence, including unreachable pairs.
- `MissingEdgeConnectivity`: native cut-set edge connectivity and minimum-degree consequence for a missing edge; low-degree graphs force retention.
- `Blocking`: Lemma20's actual greedy blocking-set construction, with tie handling and no assumed blocking oracle.
- `TreePruning`: the bottleneck-MST exchange fact that some maximum cycle edge lies outside the tree. Actual sampled graph pruning is now supplied by GraphPruning below.
- `HostCounting`: finite host congestion/counting, exact weighted incidence, and conditional baseline charging. Forest existence and the graph lightness assembly remain open.
- `HubPreserver`, `BipartiteForcing`, `CounterfamilyWeight`: actual complete-bipartite counterfamilies to the exact displayed lambda upper comparisons. Genuine minimum denominators exist and are positive; every eligible output has competitive lightness at least m/6 against two faults or m/8 against three faults. Certificate counts ≤6m and ≤8m suffice, without using the sharper subtractive counts. These graph theorems do not themselves encode the extremal lambda supremum or the asymptotic contradiction.

Latest independently reviewed components:
- `CounterfamilyGrowth`: the same actual graphs rule out every constant-times-square-root bound for both competitive ratios simultaneously.
- `StretchParameters`: exact threshold gap and the preserved coarse weighted-girth lightness bound on actual graphs.
- `GraphPruning`: actual blocker/MST deletion and a retained minimum tree with the host weight bound, on a spanning host vertex set.
- `WeightedSampling`: finite weighted expectation and an actual sample attaining the corrected non-seed lower bound.

Compilation, whole-library build, axiom audit, independent kernel replay, independent semantic review, exact-commit CI, and fresh skeptical final audit are separate checks. See the checkpoint verification record rather than inferring completion from this module list.

Further independently reviewed obstruction components:
- `BlowupCertificateObstruction`: the actual six-vertex failure of Theorem 34's proposed certificate, including an actual MST and allowed input faults.
- `GenericBlowupFailure`: every-tree failure on complete bases, plus exact source cloud rounding.
- `FaultBudgetSaturation`: exact finite q>=n−2 preserver collapse, with no unconditional asymptotic-refutation claim.

## Source correspondence and remaining work

The numbered inventory in `verification/statement-map.json` includes all 37 source items. The main statements are Theorems 9–13 and 34. Theorem18 and the actual greedy blocking construction in Lemma20 are proved. Actual host-forest construction (Corollary25), host vertex-set transport for Lemma26, the optimized heavy/light sampling argument, a replacement for Theorem34’s invalid lower-bound certificate, remaining lower constructions, randomized algorithms, concentration, and runtime remain open.

External dependency Theorem 24 (Chekuri–Shepherd Eulerian Steiner-forest packing) and its multigraph use are particularly substantial. Nash-Williams tree packing is inventoried separately. These are not introduced as custom axioms. A reduction under their hypotheses alone will not count as a proof of an advertised unconditional main theorem.

## Explicit corrections

See `CORRECTIONS.md` and the independently prepared source-correction report. The full reading edition preserves the original source separately from corrected exposition.

The exact displayed lambda upper bounds in Theorems11–13 require the corrected stretch-to-girth argument; an independently checked uniform counterfamily disproves the printed comparison. The coarser polynomial upper tradeoffs and the main2f threshold are not refuted. Independently, Theorem34’s MST-cloud denominator certificate fails; the theorem itself has not been disproved. This is a proof gap requiring a replacement construction.

The `f=1` sampling issue and polynomial-algorithm threshold mismatch require changes to the displayed construction/proofs. The real-eta vote threshold requires integer rounding. The finite-uniform higher-competition bound retains the seed's baseline weight. The main `O_eta(lambda)` formulation is compatible with the repaired `1 + O(lambda/eta)` bound. Typographical fixes are listed separately from these substantive changes.

No final completion or public research-site link is authorized by a partial component checkpoint. A fresh independent skeptical end-to-end audit is required after the proof scope is actually finished.
