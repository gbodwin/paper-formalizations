# Light Edge Fault Tolerant Graph Spanners

Greg Bodwin, Michael Dinitz, Ama Koranteng, and Lily Wang.
Source: [arXiv:2502.10890v2](https://arxiv.org/abs/2502.10890v2), 25 April 2025; ICALP 2025.

**Active partial formalization. Corrected exact-extremal finite simple-graph upper bounds at competition 2f and floor((2+eta)f), and the Section4.1 finite lower family, are proved. Printed lambda arguments remain refuted; Theorem34, the weighted multigraph main extension and polynomial-time theorem remain open.**

**Latest dependency checkpoint: 166 modules / 1093 declarations, all local gates and reciprocal exact-source review PASS. Both constructed upper bounds now use the actual exact-n extremal supremum at stretch+1. Fresh exact166 full CI is pending;152 is fully green. Full-paper completion and final audit remain separate. See verification/CHECKPOINT.md.**

## Corrected exact-extremal upper bounds (166-module packet)

For s=(1+epsilon)*(2k-1), the new final theorems construct a true minimum-weight
fault-connectivity preserver Q and an actual f-EFT s-spanner H with

    competition 2f:             lightness(H | Q) <= 1 + 16 sqrt(f) lambda(n,s+1)
    competition floor((2+eta)f): lightness(H | Q) <= 1 + 8 lambda(n,s+1)/eta.

Here lambda is now the actual supremum over weighted graphs with exactly n
vertices and weighted girth above the stated argument. It is not an assumed
bound or an at-most-n substitute. At n>=2 and argument>2, the totalized Lean
definition equals the literal actual-graph supremum. The n<2 boundary is defined
as zero, and zero optimum uses the existing total real-division convention.

The proof transports actual graph/MST weights through reindexing and subdivides
a positive edge of an internally chosen bottleneck MST into two equal positive
halves. This adds exactly one vertex, preserves both weights and lightness, and
does not decrease weighted girth. Iteration therefore proves the exact-order
monotonicity needed to compare every actual subtree host with the original
order. The already proved coarse girth bound establishes that the spectrum is
bounded. Sampling, pruning, real supremum comparison, genuine host transport,
heavy/light charging, congestion two, forest construction, and minimum-preserver
choice are then joined without a supplied packing or extremal-bound oracle.

The final scope is finite undirected simple graphs with globally nonnegative
real edge weights strictly positive on actual edges; f,k are positive natural
numbers and epsilon,eta are positive reals. The additive seed baseline one and
exact higher-budget floor remain explicit. All 152 parent proof files are
unchanged. This closes the corrected exact-lambda upper interface at s+1.
The printed argument (1+epsilon)*2k remains refuted by the existing counterfamily;
this checkpoint does not restore it.

A separate finite-uniform boundary is made explicit: an actual two-vertex unit
tree has extremal lightness at least one for every girth threshold. Consequently
no single constant gives lambda(2,(1+epsilon)*2) <= C*2/epsilon for every epsilon>0.
The all-positive-epsilon wording of cited Theorems4/17 needs a bounded-epsilon
convention or an additive baseline if read as such a finite-uniform assertion.
This does not refute a fixed-epsilon asymptotic assertion with a parameter-dependent
large-n onset, nor the O_epsilon coarse bounds. The source's Big-O onset ambiguity
is retained explicitly; no new asymptotic theorem-false claim is made.

All strict production, root/index, defining-module axiom and fourteen official
kernel replay gates pass, together with independent exact-source semantic review.
Fresh exact 166 full CI remains a separate pending gate. The exact 152 parent is
fully green: run38185593849, completed2026-10-12 00:29:25 UTC,1045 paper declarations,
and290 complete-repository kernel replays. Historical sections below describe
then-current stages only and do not override this status or the numbered map.

Remaining whole-paper obligations are the weighted multigraph main extension,
actual efficient algorithms and concentration/runtime (including packing runtime),
a valid Theorem34 lower denominator certificate with the claimed scaling, the
literal every-n/epsilon-uniform Theorem10 lower domain, cited-background/source
coverage reconciliation, and a fresh skeptical end-to-end audit. A proved finite
existence statement does not establish the polynomial-time clause.


## Contracts and mathematical scope

- Finite undirected simple graphs, arbitrary finite edge fault sets, and real edge weights. Walk-based spanner semantics covers disconnected input graphs. Weighted distance is supplied by the already checked LightSpanners library.
- Greedy correctness assumes nonnegative edge weights and stretch at least one. Positivity on actual graph edges and positive denominator are separate hypotheses for lightness results.
- Fault budgets are natural numbers. A real budget is interpreted by its floor; the higher competition parameter uses `2*f + floor(eta*f)` and requires `floor(eta*f)+1` host votes.
- The source extends upper bounds to multigraphs. This extension remains open and will not be inferred from a simple-graph result.
- Asymptotic constants, integer-rounding requirements, small parameter cases, and the base preserver weight must remain explicit. Neither a final inequality nor a packing theorem is hidden in a definition of the construction.

## Historical component chronology

The paragraphs below record progress when each packet was introduced. Earlier open packing/host/upper dependencies have since been discharged as described in the current166 section and numbered statement map. Historical pending-CI statements are superseded by later terminal receipts.

### Initially checked component modules

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

## Actual cut, contraction and partition foundations

Eight further components develop the external packing dependency without assuming its conclusion:
- `ConnectivityCuts` and `MinimalConnectivityCore`: native simple-graph edge reachability is equivalent to actual separating-cut cardinality bounds. A genuine basic instance with distinct connectivity islands supplies a proper minimal deficient core, closed under connectivity classes and containing at least two vertices.
- `MultigraphCutTransport` and `ContractedCoreCuts`: mathlib's actual edge-identified `Graph.map` retains every parallel edge through complement contraction. Every separating contracted-core cut has the proved cardinality lower bound, with the outside-vertex case handled by cut complementation.
- `MultigraphPartitionCounts` and `CorePartitionBudget`: exact double counting counts internal crossing edges twice and the outside cut once. Every genuine nontrivial surjective core partition meets the required spanning-tree packing partition inequality. Empty and singleton partition budgets are separated explicitly.
- `MultigraphFaultConnectivity` and `ContractedCoreConnectivity`: faults delete original edge identities before native surviving-walk reachability is tested. The exact cut characterization is proved using actual post-deletion components. Contraction preserves this connectivity, the semantics agrees with native simple-graph edge reachability, and the selected core is genuinely fault-connected after contraction. A parallel-edge example checks that deletion precedes simplification.

These prove the integral finite simple-input minimal-core specialization and actual counting obligations used in CS09 Lemmas 2.4–2.5; they do not construct multiple edge-disjoint spanning trees. Nash-Williams/Tutte, Mader splitting, expansion and the general Steiner-forest packing join remain open. The native multigraph work here is a dependency interface, not the paper's full multigraph upper-bound extension. Exact local, replay, review and CI status are recorded separately.

## Integral native-multigraph core reduction

A further four-file packet extends the integral core step to arbitrary finite native multigraph inputs:
- `NativeMultigraphCore`: basicness quantifies over actual graph vertices. Intersecting cut sides with the true vertex set removes phantom ambient vertices before finite minimal selection. The selected core is proper, has at least two actual vertices, is closed under fault-connectivity classes and has the exact inner-cut minimality property.
- `NativeCoreContraction`: explicit inclusion of the core in the actual vertex set provides its real mapped endpoints. Every separating contracted cut has the threshold bound, and the joined theorem constructs actual post-fault native walks from the original basic-instance hypotheses.
- `NativeCorePartitionBudget`: actual nontrivial surjective partitions satisfy the crossing-edge budget in the native multigraph, retaining all original parallel identities and excluding outside loops.
- `MultigraphContractionSize`: the contracted outside vertex has an explicit preimage; the full-vertex invariant is stated separately from finite vertex-type cardinality. A core of at least two vertices strictly lowers that cardinality, which is actual graph order only under the full-vertex invariant.

The four sources and 68-module aggregate/548-declaration audit/kernel gates pass locally. The independent four-file semantic review returned component PASS at23:21:37, recorded in FOURTEENTH_SEMANTIC_REVIEW.md. The exact proof CI38094267232 passed in full23:42:14. This integral generalization does not prove the weighted fractional lemma, Nash-Williams/Tutte, Mader splitting, forest expansion, packing existence or runtime.

## Original-identity native forest foundations

Four newer sources construct actual forest objects needed for the future packing proof:
- `NativeBridgeSemantics`: actual post-deletion disconnection gives a cut contained in the deleted original identities; native cut bridges are exactly endpoint-disconnecting edges. An all-bridge native graph is genuinely simple.
- `NativeForestSemantics`: deleting a pair of endpoints always removes at least its chosen original edge; the reverse implication requires genuine native simplicity. All actual native edges are bridges exactly when the native graph is simple and its ordinary adjacency graph is acyclic.
- `NativeForestSelection`: one original identity is chosen consistently per unordered simple edge. This injective representative construction lifts an actual simple subgraph and constructs a native spanning forest with all original actual vertices and exactly preserved reachability. Loops and parallel cycles are removed by proved selection rather than silently ignored before faults.
- `NativeForestCardinality`: an actual edge bijection gives the exact connected forest count against actual vertexSet. Connected input constructs a real original-edge spanning tree and the finite native connectivity lower bound. Phantom ambient vertices are never counted as graph vertices.

All four strict production sources,72-module root/index,577-declaration allowed-axiom audit and four official kernel replays pass locally. Exact hashes are frozen in FIFTEENTH_SOURCE_HASHES.json. The independent four-file semantic review returned component PASS at23:33:43, recorded in FIFTEENTH_SEMANTIC_REVIEW.md. Exact72 proof CI38095126415 passed in full23:42:21; the separate report-commit CI is tracked in the checkpoint record. These are single-forest/tree foundations; multiple edge-disjoint spanning trees, Mader splitting and full packing existence remain open.

## Actual partition refinement and exchange foundations

Six newer sources continue the finite tree-packing dependency:
- `NativePartitionCriterion`: original-edge crossing counts on actual vertex labels. The full finite partition condition yields actual fault connectivity and its positive case yields connectedness. The one-tree sufficiency case constructs a real native spanning tree; general k-tree packing remains open.
- `NativeBlockRefinement`, `FinitePartitionRefinement`, `PartitionRefinementTermination`: actual within-block graphs and component partitions, the least splitting color, strict ordered-pair measure decrease, and stabilization within n² rounds. The terminal partition is below the initial one and above every common connected refinement, so it is not an arbitrary singleton substitution. This is a round bound, not a full algorithmic runtime result.
- `NativeExchangeConnectivity`: genuine original-edge walk substitution for an exchange. The removed edge's replacement route remains an explicit local premise; constructing the required exchange/cycle and proving the maximality contradiction remain open. If the removed edge is external to all blocks, within-block walks survive without a replacement premise.
- `NativeForestDensity`: a disconnected finite forest extends strictly to an actual spanning tree, yielding at most n−2 original edges. The density condition therefore forces a genuine native nonbridge, with actual vertex domains and original edge identities.

All six strict production builds,78-module root/index and631-declaration audit pass locally. All six new official kernel replays pass; fresh six-file semantic review returned component PASS at00:06 UTC on11 October (SIXTEENTH_SEMANTIC_REVIEW.md), and exact78 CI remains pending. These match parts of Kaiser's finite partition/exchange proof route; the general Nash-Williams/Tutte theorem, Mader splitting and CS09 forest packing remain open.

## Current source correspondence and remaining work

The numbered inventory in verification/statement-map.json covers all37 source items.
The finite native Nash-Williams equivalence and Eulerian forest existence are proved;
actual simple doubling, projection, host construction, sampling and heavy/light analysis
are joined to both corrected exact-extremal finite simple-graph upper bounds. Section4.1
has an actual unbounded real-stretch lower family with explicit finite size conditions.

Weighted multigraph main upper bounds, the polynomial-time packing and randomized
algorithms/concentration, Theorem34's replacement lower certificate, Theorem10's literal
uniform finite lower wording, and remaining cited-background coverage are open. These
are not supplied as custom axioms. A fresh end-to-end audit is still required.

## Explicit corrections

See `CORRECTIONS.md` and the independently prepared source-correction report. The full reading edition preserves the original source separately from corrected exposition.

The exact displayed lambda upper bounds in Theorems11–13 require the corrected stretch-to-girth argument; an independently checked uniform counterfamily disproves the printed comparison. The coarser polynomial upper tradeoffs and the main2f threshold are not refuted. Independently, Theorem34’s MST-cloud denominator certificate fails; the theorem itself has not been disproved. This is a proof gap requiring a replacement construction.

The `f=1` sampling issue and polynomial-algorithm threshold mismatch require changes to the displayed construction/proofs. The real-eta vote threshold requires integer rounding. The finite-uniform higher-competition bound retains the seed's baseline weight. The main `O_eta(lambda)` formulation is compatible with the repaired `1 + O(lambda/eta)` bound. Typographical fixes are listed separately from these substantive changes.

No final completion or public research-site link is authorized by a partial component checkpoint. A fresh independent skeptical end-to-end audit is required after the proof scope is actually finished.

## Actual tree quotients and terminal-color obstruction

Seven further modules supply the source proof's real terminal-quotient argument:
NativeCorePackingCriterion, NativeForestQuotient, NativeQuotientCardinality,
NativeQuotientReachability, NativeCrossingNonbridge, NativeColorCrossings, and
NativeTerminalDensity. An induced native core satisfies the actual partition
criterion. Contracting genuinely connected fibers preserves crossing bridges,
actual walks lift/project, and a native tree has exactly one fewer crossing
identity than actual image vertices. Edge colors partition these identities
exactly. Given genuine first-color trees and connected terminal fibers, the
partition condition forces a last-color crossing edge with a real alternate
path after deleting that same original identity. No cycle witness is assumed.

All seven strict production builds,85-module root/index and667-declaration
allowed-axiom audit pass locally. All seven official replays also pass. The fresh seven-file semantic review returned component PASS at00:17:30 UTC
on11 October (SEVENTEENTH_SEMANTIC_REVIEW.md); exact85 CI remains pending. Minimum-level selection, the tree exchange,
lexicographic maximality, full tree/forest packing, splitting and the main upper
bounds remain open. The first-color trees are inputs to this induction step,
not a claim that the full requested packing has already been constructed.

## Constructed refinement, finite levels and replacement routes

NativeEdgeLevels, NativeNonbridgeCore, NativeMinimumCycleLevel,
NativePartitionLabels, NativeRefinementCycleWitness and NativeSplitColor
construct the next source obligations. Actual finite setoid labels and
connected fibers come from the real least-color terminal iterate. Native cut
symmetric difference proves that removing all bridge identities preserves an
alternate path for every nonbridge. Minimizing actual finite edge levels then
constructs a same-color replacement path entirely inside the selected level
block, including parallel-edge semantics. The joined theorem starts with the
genuine first-color-tree/last-color-disconnected inductive countercase; it no
longer assumes terminal labels, connected fibers, a minimum edge or that route.
The exact next splitting color is proved to be an earlier tree color.

The six new strict production sources,91-module root/index and704-declaration
allowed-axiom audit pass locally. All six official kernel replays also pass.
Fresh frozen six-file semantic review returned COMPONENT PASS at00:40:40 UTC
on11 October; see EIGHTEENTH_SEMANTIC_REVIEW.md. Exact91 CI remains pending. Actual full tree exchange and
lexicographic maximality remain open, along with packing/splitting and the
main upper bounds. Classical finite choices are not an executable runtime result.

## Constructed lower-level native tree exchange

The next six modules construct the actual earlier-color local exchange rather
than assuming its cycle edge. A real old tree supplies the inserted edge's
alternate route. Native bridge-core selection then constructs an old edge at a
strictly lower partition level, with a real replacement route inside that
level's block. Restriction and terminal-truncation lemmas identify this level
with the exact original graph's global level function. The exchanged graph is
proved to be a genuine native spanning tree by connectivity and exact original
edge count; loops and parallel cycles are excluded as a consequence.

A separate general helper proves all-stage connectivity preservation when the
removed edge's within-level replacement route and next-stage separation are
supplied. The concrete two-color swap, lexicographic maximal-decomposition
choice and contradiction, full packing and splitting are still open. All97
strict production/root/index and743-declaration audit gates pass, as do all six
new official kernel replays. Fresh six-file source/semantic review returned COMPONENT PASS00:59:21 UTC on
11 October; exact97 CI remains pending. See NINETEENTH_SEMANTIC_REVIEW.md and
CHECKPOINT.md for the separate gates.

## Actual color swap and finite maximal decomposition

NativeColorExchange defines the literal two-original-identity swap and proves
its exact class and native graph identities. NativeColoredExchange constructs
the changed color's genuine tree, lower global level, exact split boundary and
within-level route from the local source countercase. The global preservation
helper retains explicit two-route premises. NativeDecompositionMaximum chooses
a true maximum of the actual finite refinement signatures over all colorings
with the earlier-tree property, starting from an explicit inductive seed.
The finite horizon is an explicit parameter; this choice is noncomputable and
is not an efficient executable algorithm.

All100 strict production/root/index gates and765-declaration audit pass locally;
all three new official kernel replays also pass. Fresh three-file semantic review returned COMPONENT PASS at15:17 UTC on
11 October; see TWENTIETH_SEMANTIC_REVIEW.md. Exact100 proof CI38150227125 passed completely at15:46:28 on11 October, including the clean build, repository indexes, all-declaration audit and every project kernel replay. The report-only successor964b388d also passed its exact CI38150740826 completely at15:56:13.
Related-pair counts strictly rank comparable refinements; equal counts alone
do not identify partitions. The chosen finite horizon remains explicit.
The strict-improvement/maximality contradiction, new-refinement prefix rigidity,
full source-countercase assembly, induction, general packing and splitting remain
open. Both97 proof and review-report checkpoints are now full exact-CI green.


## Actual refinement rigidity and maximality contradiction (106-module packet)

The six new modules NativePriorityComparison, NativeSignatureStages,
NativeRefinementRigidity, NativeExchangeImprovement, NativeImprovingExchange,
and NativeMaximalCountercase derive comparison of the genuine recomputed
refinement sequences, then construct the actual lower-level two-edge color
swap and prove its strict signature improvement. From the real partition
criterion and k earlier native spanning trees, a disconnected last-color pair
produces an admissible improved coloring at the proved quadratic actual-vertex
horizon. Hence a truly maximal admissible coloring has every pair connected in
its last color. Original edge identities, including parallel edges, are retained.

All six strict production builds, the106-module root/index, the exhaustive800-
declaration allowed-axiom audit and six official kernel replays pass locally.
Prior100 sources and objects were reused unchanged; the new full clean106 build
is an exact-commit CI obligation. Reciprocal exact-source semantic review returned COMPONENT PASS at16:00 UTC
on11 October; see TWENTYFIRST_SEMANTIC_REVIEW.md. TWENTYFIRST_SOURCE_HASHES.json records the frozen component sources.

This closes the recomputed-refinement rigidity and strict-improvement/maximality
contradiction, not the whole packing dependency. The existence of earlier-tree
seeds for all k by induction, extracting and assembling the final disjoint tree
family, Mader splitting, Steiner expansion and the unrestricted paper upper
bounds/runtime remain open. No full-paper audit or completion is claimed.


## Constructed finite native tree packing (109-module packet)

The partition criterion now constructs its own k-tree family by induction.
NativePackingExtension literally retains the selected residual tree as the next
earlier color and sends only unused residual identities to a fresh last color.
NativePackingInduction starts with zero earlier trees, constructs a true finite
maximum from the previous inductive family, proves the residual connected using
the checked improvement contradiction, and extracts a genuine original-edge
spanning tree. NativeTreePacking extracts the color classes and proves pairwise
edge-disjointness, actual native connectedness, every-edge bridge property and
the exact |V|-1 count. No inductive seed or final packing is an input to the
final theorem. Finite edges and a finite nonempty actual vertex set are explicit;
phantom ambient vertices do not enter the criterion or cardinalities.

All109 root/index and814 declaring-module allowed-axiom checks pass, with three
strict new production builds and all three new official kernel replays. Prior106
sources/objects are unchanged locally; full clean109 CI is separate. Reciprocal
three-file exact-source semantic review returned COMPONENT PASS at17:19 UTC;
see TWENTYSECOND_SEMANTIC_REVIEW.md. The106 baseline already
passed full exact CI38153732739 at16:30:23 on11 October.

The partition-sufficiency multiple-tree packing dependency is now constructed.
Mader splitting, Steiner expansion, the required connectivity-preserving forest
family/congestion, weighted fractional steps and full EFT bounds/runtime remain
open. This is not a full-paper completion or final skeptical audit.


## Native tree-packing equivalence (112-module packet)

NativePartitionLower proves the crossing lower bound for any occupied partition
of an actual connected native graph. Its fibers may be disconnected: only the
whole crossing quotient is required connected. NativePackingNecessity sums this
bound over genuine edge-disjoint connected spanning members and bounds their
union by the original partition crossings. NativePackingEquivalence joins that
necessity direction to the constructed induction, giving the finite native
Nash-Williams/Tutte equivalence in printed Theorem22. The actual vertex domain
is finite and nonempty; the ambient edge-ID type is finite. The result includes
k=0 as well as the printed positive-integer scope. The packing predicate asserts
only actual original-edge trees and pairwise edge disjointness.

Three new strict production builds,112 root/index and all822 declaring-module
allowed-axiom checks pass. All three new official kernel replays pass; fresh reciprocal
source review returned COMPONENT PASS at17:27 UTC (TWENTYTHIRD_SEMANTIC_REVIEW.md). Prior109 source/objects remain unchanged locally;
the full clean exact112 CI is separate. The109 existence checkpoint7047d2e0 has
all local gates and review passed, with exact CI38159252903 running;106 remains
the full exact-CI baseline. This closes the finite tree-packing equivalence but
leaves Mader splitting, general Eulerian connectivity-preserving forests,
Steiner expansion, required congestion, weighted fractional dependencies and
the full EFT bounds/runtime open.


## Native Eulerian splitting and single-Steiner reduction (125-module packet)

Thirteen new modules prove the uniform-threshold Eulerian splitting dependency
needed in the CS09 forest argument. The final theorem starts with a finite native
multigraph, even actual degrees and required terminal pairs with cut threshold
2k. The exact predicate FaultConnected(2*k) tolerates strictly fewer than2*k
deleted original edge identities; it does not promise tolerance of2*k deletions.
For k=0 only required endpoint membership remains substantive.

Finite tight-set maximization and uncrossing construct a distinct incident-edge
partner. The native split retains surviving old IDs, allocates one fresh ID,
and proves the exact cut change. A proved handshake identity transfers even
degrees to even cuts and back. Every constructed split preserves the required
connections, all vertices and parity while reducing actual nonloop center
incidence by exactly two. Strong induction constructs a finite split trace and
then removes the exhausted center. The resulting native terminal graph has the
exact original terminal vertex domain, even degrees and the required connections.
Center loops, repeated/parallel identities, equal other endpoints, isolated
vertices, empty terminal domains and zero center incidence are handled.

The final result does not assume Mader splitting, an admissible-pair oracle,
preselected maximum, packing, or the desired final cut inequality. It proves
the uniform2k Eulerian case, not general non-Eulerian Mader or simultaneous
preservation of unequal thresholds. All112 prior proof bytes are unchanged.
Strict production builds,125 root/index, all972 allowed-axiom checks and all13
new official kernel replays pass; Flow's independent source audit returned
COMPONENT PASS at20:10 UTC. Exact full125 CI is still a separate pending gate.

Original-edge path/forest expansion through the trace, disjointness after
expansion, forest pruning and the multi-island induction remain open. Hence
the full Eulerian forest packing/congestion result, weighted/fractional joins,
main EFT upper bounds and runtime are not complete. No new source error is
asserted. See TWENTYFOURTH_SCOPE.md and TWENTYFOURTH_INDEPENDENT_FLOW_AUDIT.json.


## Actual split-trace forest lifting (129-module packet)

Four new modules prove original-edge family expansion through the actual finite
split trace and join it to the proved Eulerian single-center reduction. A
selected fresh output ID expands to its two deleted original IDs, while every
selected surviving old ID retains its identity. Actual output-edge membership
excludes deleted IDs, proving that disjoint output families expand to disjoint
original-edge families even with loops and parallel edges. Every output link
is replaced by an actual old link or the two old center links, and walk
induction proves genuine member-wise connectivity rather than assuming it.

Trace induction handles changing edge-ID types. The exact terminal-domain graph
maps into the final graph with unchanged selected IDs. The existing native
forest selector then prunes each raw expansion: membership decreases, all
connections survive, every retained edge is a native bridge, and disjointness
is preserved. The final joined theorem constructs the same actual single-center
reduction, exact terminal vertex domain, even degrees and required
FaultConnected(2*k), with a lifting certificate for arbitrary supplied disjoint
output families. The output family need not already be acyclic.

The family on the reduced graph remains an explicit input to the lifting
conclusion. The multi-island packing induction, core-contraction expansion and
combination, full Eulerian forest packing/congestion, weighted/fractional joins,
main upper bounds and runtime remain open. No new source correction is asserted.
All125 previous proof files are unchanged. Strict production builds,129
root/index,988 allowed-axiom declaration checks and all four new official
kernel replays pass, as does independent exact-source component review.
The new exact129 full CI remains a separate gate.


## Constructed finite Eulerian forest packing (140-module packet)

The final theorem exists_native_eulerian_forest_packing constructs k
edge-disjoint native original-edge forests. Every original pair that survives
strictly fewer than2k deleted edge identities is joined in every forest. Each
retained edge is a genuine native bridge; parallel IDs are not identified.
The graph has finite vertex and edge-ID types, every ambient vertex is actual,
and every native degree is even, with loops counted twice. Empty/singleton
vertex domains, isolated vertices, loops, parallel edges and k=0 are covered.

The induction on the actual full vertex count now supplies the previously
missing recursive forest families. The one-island branch constructs spanning
trees via the proved native partition theorem. The basic multi-island branch
selects a proper minimal core of size at least2, internally constructs its
disjoint spanning trees, contracts it to a strictly smaller actual Eulerian
graph, and expands the recursively constructed quotient forests through actual
original links and fiber paths. Mixed edge collisions are excluded because an
internal fiber edge becomes a genuine quotient loop and cannot belong to a
quotient forest. The singleton-island branch uses a literal vertex equivalence
to expose the center, the proved Eulerian splitting trace, and the strict
cardinality decrease on the domain excluding that vertex. Reflexive center
demands are restored. Original-edge pruning preserves all required connections.
No splitting theorem, admissible-pair oracle or final packing primitive is assumed.

This is the mathematical existence portion of printed Theorem24, in a native
full-vertex representation of the finite graph domain. The polynomial-time
clause is NOT proved. The uniform even-degree splitting special case is
constructed internally; no general non-Eulerian or unequal-threshold Mader
theorem is claimed. There is not yet an explicit wrapper for native graphs
whose ambient type includes phantom nonvertices. The joins to the doubled
simple-graph congestion/host family, fractional/weighted estimates and main
EFT upper bounds remain open. No new source correction is asserted.

All129 parent proof bytes are unchanged. Eleven new strict production builds,
140 root/index,1017 allowed-axiom declaration checks, all11 new official kernel
replays and independent exact-source skeptical component review pass. Fresh
exact140 full CI is a separate pending gate; no whole-paper completion or
final-audit claim is made. See the TWENTYSIXTH scope, local-gate and review receipts.


## Constructed coarse higher-competition upper bound (144-module packet)

Theorem exists_eft_spanner_rounded_coarse_bound now constructs both a true
minimum-weight connectivity preserver Q and an actual f-EFT spanner H of
stretch (1+epsilon)*(2*k-1), with

    competitiveLightness H Q w <= 1 + 8*(8 + 2048/epsilon * n^(1/k))/eta.

The precise competition budget is floor((2+eta)*f). The domain is finite simple
graphs, globally nonnegative real weights that are strictly positive on actual
edges, positive natural f and k, and arbitrary positive real epsilon and eta.
No upper restriction on eta is assumed. The seed baseline one is retained;
zero optimum weight is covered by the existing total real-division convention.

The constructed native Eulerian packing is transferred to actual simple
forests by exact degree and restricted-edge isomorphisms. The actual doubled
two-subdivision has even degrees. Its internally constructed disjoint forests
project with congestion at most two; the existing genuine component-host and
greedy-weight analysis then applies. Exact floor arithmetic supplies the surplus,
and finite minimization supplies Q. No forest/host family or optimality certificate
is an input to the final existence theorem.

This establishes the corrected finite coarse upper consequence associated with
Theorem12's O_{epsilon,eta}(n^(1/k)) upper bound. It does not restore the refuted
exact lambda expression, prove the square-root-f bound at competition 2f, prove
the main multigraph extension, certify lower statements, or establish runtime.
The full paper remains incomplete and requires a fresh final skeptical audit.

All 140 prior proof files are unchanged. Four new strict sources, the 144-module
root/index, all 1027 defining-module declaration axiom checks, four official
kernel replays and independent exact-source component review pass. Fresh exact144
full CI is a separate pending gate;129 at f59a915d is the terminal full-CI baseline.
Both125 and129 completed all clean-build/index/audit/replay gates;140 is running. See TWENTYSEVENTH_SCOPE.md and receipts.


## Constructed square-root-f upper bound at exact competition 2f (152-module packet)

Theorem exists_eft_spanner_square_root_bound constructs a true minimum-weight
2f-fault connectivity preserver Q and an actual f-EFT spanner H of stretch
(1+epsilon)*(2*k-1), with the explicit finite bound

    competitiveLightness H Q w <= 1 + 16 sqrt(f) (8 + 2048/epsilon * n^(1/k)).

Finite simple graphs, globally nonnegative real weights strictly positive on
actual edges, positive natural f,k and epsilon>0 are explicit. The additive seed
baseline is retained. Zero optimum uses the existing total real-division
convention. No forest family, host family, local blocking certificate or optimum
certificate is supplied to the final existence theorem.

The actual heavy/light argument partitions candidates at residual blocker cap
r=floor(sqrt(f)). Heavy candidates use sampling probability 1/(2r); light candidates
retain cap f but receive 2r+1 unblocked actual component hosts. Their respective
weight bounds are 8r L w(Q) and 8f L w(Q)/(2r+1), where
L=8+2048/epsilon*n^(1/k). The exact integer inequality f<=r(2r+1), including f=1,
gives the stated bound. Only seed blockers disqualify actual seed-tree hosts.
Original edge identities, injective host-domain transport and congestion two
are preserved. Internally constructed doubled-subdivision forests discharge the
structural inputs at q=2f; finite minimization supplies Q.

This establishes the coarse O_epsilon(sqrt(f)*n^(1/k)) upper consequence associated
with printed Theorems 11/29. It does not restore the refuted exact lambda expression.
Theorem 34's denominator-certificate gap is a separate unresolved lower-bound issue.
The full main multigraph extension, efficient randomized algorithms/runtime and
fresh whole-paper final audit remain open. Historical sections below retain their
then-current scope and must not override this latest status.

All 144 parent proof sources are unchanged. Eight strict production builds, the
152-module root/index, all 1045 defining-module declaration axiom checks, eight
independent official kernel replays and reciprocal exact-source semantic review
pass. Fresh exact 152 full CI is a separate pending gate;144 at c1538fd1 is the fully
green baseline (run 38175414276, completed21:48:34 UTC, 11 October 2026;282 repository
replays). The 140 dependency baseline also passed completely.
