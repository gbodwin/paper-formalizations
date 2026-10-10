# Light Edge Fault Tolerant Graph Spanners

Greg Bodwin, Michael Dinitz, Ama Koranteng, and Lily Wang.
Source: [arXiv:2502.10890v2](https://arxiv.org/abs/2502.10890v2), 25 April 2025; ICALP 2025.

**Active partial formalization. The main upper bounds, Theorem 34 lower bound, and polynomial-time theorem remain open. The Section 4.1 lower family has a new explicit finite proof; see its separate gate and domain record below.**

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
- `HostCounting`: finite host congestion/counting, exact weighted incidence, and conditional baseline charging. Forest existence and the unrestricted graph upper bound remain open.
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

Reviewed actual graph wrappers:
- `HostGraphSampling`: an explicit finite sample, cleaned/pruned graph and retained genuine MST prove the corrected non-seed weight bound for an actual supplied host tree. The host must span the fixed vertex type, its edges must lie in the seed, and every candidate blocker set must avoid the host tree. For positive weights and at least two vertices, the corrected coarse girth theorem gives an explicit candidate weight bound.
- `LargeCloudCertificate`: connected spanning subgraphs really give q-fault connectivity preservers after blowup when cloud size exceeds q. The enlarged-cloud conclusion has worse source scaling and does not restore Theorem34.

Section 4.1 foundation batch (see the checkpoint record for its gate status):
- `ParallelSubdivision`, `DisjointCycleFaults`, `SubdivisionCleanColor`, and `SubdivisionPreserver`: actual colored subdivisions, fault localization, and full all-fault connectivity transport including isolated branch vertices.
- `CycleCertificate`, `SubdivisionWeight`: actual (2f−1)-fault unit-edge certificate for the native cycle graph, exact vertex count, and explicit unit-weight budget.
- `CycleLinearization`, `PotentialForcing`: actual cut-cycle path containment and walk-potential edge forcing. The new batch below constructs and rotates the heavy-edge potential and joins the lower ratio.


Actual Section 4.1 lower-family batch (local build, axiom audit, all kernel replays and independent semantic/source review passed; exact-commit CI tracked separately):
- `SubdivisionForcing`, `CycleRotatedPotential`, `CycleCoreRetention`: actual f-edge fault sets and a rotated real potential force every heavy core-cycle edge in every eligible output.
- `CoreGraphWeight`, `CycleCompetitiveLower`: the retained core gives the numerator; the actual unit-edge certificate and positive genuine minimum give the denominator. The finite bound is W/(2f), with no assumed final lower inequality.
- `CycleLowerFamily`: for positive integers f,k and q≤2f−1, an actual graph with n=(m+3)(f+1) vertices, m+2≥2k, has competitive ratio at least n/(8f²k) for every f-EFT k-spanner. The input itself is eligible, and the family has unbounded order.
- `RealStretchLowerFamily`: for every real t≥1, rounding upward gives n/(16f²t) under m+2≥2⌈t⌉. This preserves the source's general stretch domain. The family has unbounded order for each fixed f,t. These are explicit finite/unbounded-family statements; the source's literal all-n/epsilon-uniform Theorem 10 wording is not silently substituted for them.

Conditional supplied-spanning-packing assembly, independently reviewed:
- `HostFamilyBound`: actual finite incidence joins the proved sampled/pruned host inequalities, retaining the seed baseline in `1+8fL/h`.
- `SpanningHostAssignments`: actual assignments are constructed by filtering non-seed edges against blockers. Tree count `2f+h` and congestion two prove coverage; blockers outside the seed have zero host incidence.
- `SeededSpanningPacking`: the same actual seeded greedy output is an EFT spanner and satisfies this conditional bound against a genuine optimum seed. Positivity of that optimum is proved using a supplied nontrivial tree. Global nonnegative weights and strictly positive actual input-edge weights remain explicit.

Every supplied tree spans the common finite vertex type and lies in the seed. No relation deriving such a packing from the seed fault budget is asserted. The new per-host transport below covers genuine subtree vertex domains. The conditional heterogeneous-domain assembly is supplied below. Packing existence remains open; this is not the unrestricted main upper theorem.

Actual induced-host transport (new component gates recorded separately):
- `BlockerTransport`: restricts the genuine original blocking data to an injectively embedded finite vertex set, transporting actual cycles and both members of their blocking pair.
- `HostWeightTransport`: exact unordered-edge and total-weight transport, independent of the chosen finite edge enumerations.
- `InducedHostSampling`: the actual sample/prune/MST bound applies to a supplied tree on its own vertex domain. The original graph order bounds the local exponent; empty candidate sets and singleton hosts are handled explicitly.

These per-host results require the actual mapped tree to lie in the seed, and actual non-seed candidates to avoid their blockers on that host. The global-order wrapper has no minimum-host-size premise. The following batch supplies dependent-family assignment/incidence assembly conditionally; structural packing existence remains a separate obligation.

Conditional heterogeneous subtree assembly:
- `SubtreeHostFamily`: actual candidate and tree incidence sums aggregate the proved local bounds on differing finite vertex domains, with explicit enumeration-invariance normalization.
- `SubtreeAssignments`: the actual pullback/filter assignment retains non-seed edges precisely when their original blockers avoid the mapped tree. At least 2f+h hosts containing both endpoints and congestion two prove h surviving votes.
- `SeededSubtreePacking`: the same actual optimum-seeded greedy output satisfies the spanner guarantee and the ratio bound 1+8fL/h. Zero denominator is treated explicitly using the existing total division convention; positive denominator is not asserted in that case.

Each supplied tree lies in the actual seed and has an injective vertex embedding. The graph and tree orders can differ, with no minimum-order premise. The structural joint-endpoint coverage and congestion remain supplied assumptions; deriving them from the seed's fault budget still requires the packing theorem. Global nonnegative weights and positive actual input-edge weights are explicit. See the separate gate record for these newer sources.

Actual supplied-forest reduction and real-eta rounding:
- `ForestComponents` and `ForestComponentPacking`: every supplied forest is split into its native connected-component trees. The finite sigma-index construction preserves actual edge congestion and produces enough joint-endpoint tree hosts from forest reachability.
- `SeededForestPacking`: the optimum seed's native (q+1)-edge connectivity for missing input edges is proved and used to join the actual recursive output. Supplied acyclic subgraphs must preserve these connected pairs, number at least q+1, have congestion two, and satisfy q+1≥2f+h.
- `RoundedCompetition`: exactly floors the real competition budget and proves the repaired finite coefficient, retaining baseline1. The actual output has the conditional bound 1+8L/eta for all eta>0, where L=8+2048/epsilon*n^(1/k). There is no hidden eta upper restriction.

These statements still require an actual supplied forest or subtree packing. The existence theorem, not any final weight inequality, is the remaining structural premise. The rounded theorem is a coarse finite graph bound; it does not certify the printed lambda comparison or the optimized heavy/light factor. Gate evidence is tracked separately below.

## Actual simple-subdivision packing reduction

- `SubdivisionFaultProjection` and `SubdivisionConnectivity`: actual failed half-edges are projected injectively to failed base edges. A finite color-count argument proves native core edge-connectivity is multiplied by the number of subdivision copies.
- `SubdivisionDegrees`: the actual doubled simple subdivision has even core degrees and degree-two branch vertices. Branch vertices cannot lie in a nontrivial edge-connectivity island of threshold at least three. No global connected Euler-tour claim is made.
- `SubdivisionCoreProjection`: only complete two-half-edge paths produce projected original edges. Actual core-to-core walks project, including stationary reversals. Native spanning forests are then constructed without losing reachability.
- `SubdivisionPackingProjection`: edge-disjoint subdivision subgraphs project with congestion at most the copy count. Each original-edge host is charged to an actual half-edge at a fixed endpoint, and native forest trimming can only reduce congestion.
- `SeededSubdivisionPacking`: these constructions join the same actual optimum-seeded recursive output. The required edge-disjoint subdivision family, its count and preservation of native high-connectivity pairs remain supplied structural hypotheses. Existence of that family is the unresolved packing theorem, not an assumed weight bound.
- `PreserverWeightPositivity`: with positive actual input-edge weights, any true connectivity preserver has positive total weight whenever the input has an edge. Zero denominator is possible exactly for the edgeless input. This clarifies the existing explicit ratio convention rather than adding a nontriviality hypothesis.

The external existence theorem is still open. The new reduction realizes edge doubling by an actual simple graph, avoiding an unproved multigraph transport at this interface. Proving the general packing theorem may still require multigraph intermediate constructions. Optimized sampling, the Theorem34 replacement certificate and runtime remain open. New gates and review status are recorded separately.

## Source correspondence and remaining work

The numbered inventory in `verification/statement-map.json` includes all 37 source items. The main statements are Theorems 9–13 and 34. Theorem18 and the actual greedy blocking construction in Lemma20 are proved. Actual host-forest construction (Corollary25), the optimized heavy/light sampling argument, a replacement for Theorem34’s invalid lower-bound certificate, remaining lower constructions, randomized algorithms, concentration, and runtime remain open.

External dependency Theorem 24 (Chekuri–Shepherd Eulerian Steiner-forest packing) is particularly substantial. The actual simple-subdivision reduction above addresses the doubling/projection interface without proving that existence theorem. Nash-Williams tree packing is inventoried separately. These are not introduced as custom axioms. A reduction under their hypotheses alone will not count as a proof of an advertised unconditional main theorem.

## Explicit corrections

See `CORRECTIONS.md` and the independently prepared source-correction report. The full reading edition preserves the original source separately from corrected exposition.

The exact displayed lambda upper bounds in Theorems11–13 require the corrected stretch-to-girth argument; an independently checked uniform counterfamily disproves the printed comparison. The coarser polynomial upper tradeoffs and the main2f threshold are not refuted. Independently, Theorem34’s MST-cloud denominator certificate fails; the theorem itself has not been disproved. This is a proof gap requiring a replacement construction.

The `f=1` sampling issue and polynomial-algorithm threshold mismatch require changes to the displayed construction/proofs. The real-eta vote threshold requires integer rounding. The finite-uniform higher-competition bound retains the seed's baseline weight. The main `O_eta(lambda)` formulation is compatible with the repaired `1 + O(lambda/eta)` bound. Typographical fixes are listed separately from these substantive changes.

No final completion or public research-site link is authorized by a partial component checkpoint. A fresh independent skeptical end-to-end audit is required after the proof scope is actually finished.
