# Improved Upper Bounds for the Directed Flow-Cut Gap

Greg Bodwin and Luba Samborska · FOCS 2026 · [arXiv:2604.03412v3](https://arxiv.org/abs/2604.03412v3)

**Partial formalization. The main vertex and edge rounding bounds are proved; full-paper formalization remains in progress.**
This checkpoint preserves seventy-one completed components and reproducible evidence for
the documented source-proof repairs. It does not certify the whole paper or all advertised
algorithmic claims.

## Checked components

`DirectedFlowCutGap.Basic` defines actual directed simple paths as injective
vertex sequences with consecutive graph edges. It excludes both endpoints from
vertex weights and cuts, allows zero weights/costs, and uses extended nonnegative
real distances with infinity for disconnection. It proves threshold/all-path
equivalence and the exact residual-graph characterization that retains a demand
pair's two endpoints. A cut consisting only of the endpoints cannot cut an
existing path.

`DirectedFlowCutGap.MultiplicativeWeights` proves the positive-weight component
of a corrected Theorem 33 reduction. Given an explicit cost oracle that returns
admissible sets of cost at most α times their weighted cost potential, it
constructs a finite family internally. With positive lower weight w_min, it uses

- η = min(1, α w_min)
- T = ceil(log(W/w_min)/η) + 1
- Uniform inclusion fraction at most 4 α w(e) for every item e

The cost sequence, selected sets, potential growth, and marginal bound are proved,
not supplied as hypotheses. `exists_finite_mw_family` is the main declaration.
Its cost-oracle assumption is explicit; graph instantiation, preprocessing,
scale normalization and polynomial execution remain separate.
This component repairs the printed unscaled update rather than repeating its
incorrect logarithmic estimate.

`DirectedFlowCutGap.PackingCovering.strong_duality` proves finite incidence
packing/covering duality by geometric separation. It produces an attained
packing maximum and covering minimum with equal objective values, and an
optimal cover whose coordinates are at most one. Zero capacities and empty
index types are supported; every indexed hyperedge is assumed nonempty. No
LP-duality theorem is supplied as a premise. Computational complexity remains
separate from this existence and attainment theorem.

`DirectedFlowCutGap.PathExtraction` constructs loop-erased simple paths from
actual directed walks, preserving endpoints and containing its support in the
walk support. It proves finite simple-path enumeration and shortest-path
attainment on finite graphs, composition with the internal middle-vertex
weight, and equivalence between infinite distance and no directed walk.

`DirectedFlowCutGap.ZeroWeights` extends the repaired finite sampling theorem
to arbitrary nonnegative weights and approximation factors. An explicit penalty
argument derives avoidance of zero-weight items from the original oracle.
Zero avoidance is not a separate hypothesis. The theorem produces a positive
finite horizon and admissible family with inclusion fraction at most 4 α w(e).
The horizon is not claimed polynomial in input encoding length.

`DirectedFlowCutGap.TerminalPorts` constructs exactly three representatives per
vertex: a core, a permanent source, and a permanent sink. The port graph
preserves original endpoint-demand distances and feasibility, via actual path
lifting and loop-erased projection. Weights, cut costs, and weighted costs are
preserved exactly. This is the endpoint-preserving foundation for a repaired
Theorem 29; low-weight contraction and capacity replication remain separate.

`DirectedFlowCutGap.VertexFlow.strong_duality` identifies the finite incidence
model with actual directed demand/simple-path pairs and internal-vertex loads.
From a feasible fractional cut alone, it constructs an attained maximum
sum-multiflow and minimum fractional cut with equal objective values, with
optimal cut coordinates at most one. The feasible-cut premise explicitly
excludes demanded paths with no internal vertices. Empty and unreachable
demand families and zero capacities are covered.

`DirectedFlowCutGap.WitnessThinning` constructs the actual greedy list of
surviving threshold crossings. Only genuinely deleted indices are charged to
the deleted-weight budget; skipped surviving indices use the failed threshold.
It proves order, avoidance, separation, and L/(4B)<=q−1<=L under explicit
increment, prefix, terminal and deleted-mass bounds, B>=1 and L>=64B. Graph
prefix selection, endpoint accounting and the complete witness system remain
separate; the theorem assumes no monotonicity of distances along the carrier.

`DirectedFlowCutGap.VertexRounding` instantiates the repaired finite-family
sampling theorem on actual graph cuts. Its input is an explicit rounding factor
for every nonnegative cost vector; it does not assume the paper's main factor.
It separately proves the unconditional coarse factor |V| by an actual
threshold cut, so the factor domain is nonempty. The weak-distance consequence
and avoidance of zero-weight vertices are included.

`DirectedFlowCutGap.ShortcutContraction` constructs shortcut edges from actual
positive original paths through a removed set. Walk compression, expansion,
and loop erasure prove cut transfer and a weight loss bounded by that set's
total weight. With removed mass at most 1/2, doubling preserves fractional
feasibility. Permanent source/sink representatives preserve every original
demand, including demands whose original endpoint cores were removed; cut
pullback preserves cost. The complete unit-cost normalization remains separate.

`DirectedFlowCutGap.CandidateOptimization` proves that the actual capped
fractional-cut candidate problem has an attained minimum outside-cut mass.
It derives nonemptiness from a feasible capped starting vector, rather than
assuming an optimizer. An uncut demanded path forces remaining mass at least
one. Compactness supplies existence; no polynomial LP implementation is claimed.

`DirectedFlowCutGap.LevelCut` proves the deterministic level-crossing result
on actual directed paths and the single-round cutting guarantee for every
level in [0,1], including both boundaries and unreachable demands. It proves
an exact clipped-interval characterization and interval-length bound. The
uniform sampling measure and expected-cost theorem remain separate.

`DirectedFlowCutGap.FiniteSurvival` proves Maclaurin's inequality through finite
mean-preserving pair balancing. It derives the exact fixed-cardinality subset
average and exponential product bound. Its stopped-event wrapper is an
arithmetic consequence of explicit product domination; the pre-sampled
permutation/independent-level coupling to the graph process is still required.

`DirectedFlowCutGap.EpochAccounting` proves monotonicity of actual remaining
mass as labels are removed and the cut grows, then finite geometric and exact
logarithmic bounds from explicitly stated restart shrinkage and terminal-mass
premises. It does not equate current mass with epoch-start mass or assert an
unimplemented restart schedule.

`DirectedFlowCutGap.VertexReplication` builds actual sigma-type vertex clones,
with genuine path lifting and loop-erased projection. Fixed representatives
preserve endpoint demands. A cut pulls back through fully deleted fibers,
with exact vertex/weight totals and a proved cost-versus-clone-count bound.

`DirectedFlowCutGap.UnitCostReduction` assembles the repaired finite Theorem 29.
Its actual transformed instance has at most 4n² vertices and total weight at
most 3W. A unit-cost cut with factor α pulls back with cost at most 6αC.
Ports, shortcut contraction, clipping, normalization and ceiling replication
are all constructed. Empty graphs and zero objective are handled before any
division. Its bounded-instance unit-rounding oracle is explicit; no monotonicity
of exact gap parameters or polynomial implementation is assumed.

`DirectedFlowCutGap.WitnessPrefix` selects the predecessor of the first
frozen-distance crossing of1. The actual scan omits the source with zero
artificial increment cost, charges only used internal vertices, and yields
ordered distinct internal vertices outside the current cut. Actual subpaths
between selected vertices lie in the common residual graph, even when the
original demand endpoints were deleted. Global maximal-family assembly remains
separate.

`DirectedFlowCutGap.LevelCutProbability` uses actual Lebesgue measure restricted
to [0,1]. It proves measurability, exact selection/separation probabilities,
finite integrability and expected newly selected cost/cardinality bounds.
Closed separation events eliminate true residual paths, including infinite
and boundary-distance cases. This is a single-round probability result;
adaptive epoch coupling remains separate.

`DirectedFlowCutGap.PathSystemCounting` preserves indexed path multiplicities,
proves exact incidence sums and quarter-suffix floors, and constructs a base
path with score at least incidence²/(64·|I|·|V|). It derives the witness-scale
λ=256B version, label injectivity and an explicit two-charge multiplicity bound.

`DirectedFlowCutGap.MedianShortcuts` constructs the balanced median edge set
from the ordered list and transitive reachability relation. It proves at most
2n(log₂n+1) reachable nonloop edges, at most log₂n+1 mediators per vertex,
and actual simple paths of at most two edges for every reachable pair,
including backward pairs. Empty and singleton lists are covered.

`DirectedFlowCutGap.WitnessSystem` constructs a maximal finite family of actual
endpoint-safe witness lists. It proves per-label disjointness, the comparison
candidate's feasibility and cost at most 8B per list, and the stable-gate mass
bound |Π|>=M/(8Br). No maximal family or desired mass inequality is assumed.

`DirectedFlowCutGap.CandidateSchedule` constructs attained candidate minima and
the actual repeated-installation first-ready sequence. It proves the exact zero
optimum termination test, global restart/cap bounds across intervening samples,
processed-demand correctness and the original uniform initialization mass<=n³.
It supplies deterministic traces; the complete adaptive probability law remains
separate.

`DirectedFlowCutGap.FrozenEpochProbability` proves the genuine uniform
permutation prefix law and independent-level avoidance product. Actual cut
unions satisfy the exponential residual-path bound and expected prefix cost.
Stopped-event wrappers concern the joint reaches-and-survives event, with
explicit pointwise coupling premises. They do not condition a permutation on
survival and then assume it is still uniform.

`DirectedFlowCutGap.PathSystemCharging` constructs the full finite long/short
charging dichotomy, halted fan and canonical pair. At a positive stable state
with 64B<=L<=n<=L³, it proves a genuinely residual-reachable pair with true
summed separation value at least M(L/n)^(3/2) divided by
2048Br(256B)^4(log₂n+2). This is the current mass; no epoch-start substitution
is hidden in the theorem.

`DirectedFlowCutGap.UniformWeightReduction` constructs actual directed chain
expansions, with full internal-fiber traversal and endpoint-safe pullback. Its
clipped permanent-port instance has at most 6n vertices, total uniform mass at
most 2W, and cut-size pullback at most 2αW. Zero mass and empty cases are
explicit. This is a finite oracle reduction, not a runtime assertion.

`DirectedFlowCutGap.WeightSelfReduction` proves the actual heavy-vertex and
residual-graph construction with factor 1/τ+2α for 0<τ<=1/4. It trims original
paths to surviving internal endpoints and derives their residual threshold
condition. A uniform K·W^c oracle yields the finite bound
(4+2K)n^(c/(1+c)) for n>=1 and c>=0; the full asymptotic application still
requires its parameter bridge.

`DirectedFlowCutGap.SubpolynomialBounds` proves the uniform quantifier order
∀ε>0, ∃C>0, ∀n>=1 for the explicit logarithmic/ceiling epoch envelopes,
including B=4^J. It absorbs finite exceptions, proves closure under fixed
products/powers, and proves the eventual hard-regime threshold. It does not
replace the remaining algorithmic assembly.

`DirectedFlowCutGap.FiniteCutLaw` pushes the actual uniform-level measure onto
finite cut outcomes and proves its exact PMF and expectations. Supported
outcomes have genuine unit-level realizations; a zero off-support fallback
is safe. Representative levels preserve cuts and are not claimed uniformly
distributed. Adaptive composition must use the actual finite cut law.

`DirectedFlowCutGap.AdaptiveEpoch` implements an actual stopped scan. It checks
readiness and current mass before each round, embeds all performed rounds in
legal execution traces, and proves positive-epoch progress and the geometric
next-start mass decrease.

`DirectedFlowCutGap.AdaptiveRounding` constructs the exact finite product law
of a uniform permutation and actual level-cut outcomes. It proves the real
product-measure pushforward, supported prefix coupling, unconditional truncated
expectations and valid supported cuts from the finite outer recursion. Chosen
representative levels reproduce cuts; their distribution is never assumed uniform.

`DirectedFlowCutGap.EpochParameterBridge` applies charging at the state's actual
candidate cap, then enlarges only the numerical denominator to the global cap
envelope. It supplies explicit logarithmic and subpolynomial parameter adapters.

`DirectedFlowCutGap.AdaptiveCost` joins the actual active-prefix event to the
fixed-pair survival bound, takes a finite union over graph pairs, and bounds the
full epoch by its truncated cost plus the cost of overrun. A capped ceiling
horizon handles both exhaustion and small remaining label sets. The finite
PMF tower identity yields the actual outer output's expected cardinality under
explicit hard-regime and global parameter inequalities. The installation trace
derives the cap invariant. The following modules discharge uniform parameters
and derive the main vertex approximation bounds.

`DirectedFlowCutGap.FiniteAmplification` constructs independent repeated samples
and chooses an actual minimum-cost output. An expected nonnegative cost at most
B gives a failure probability at most 2^(-T) above 2B. The explicit logarithmic
sample count gives n^(-κ), and B=0 is handled separately. Its finite tower
identities support the adaptive expected-cost proof.

`DirectedFlowCutGap.EdgeModel` defines actual ordered graph edges, edge-weighted
walks and paths, edge cuts, and extended distances. Loop erasure preserves the
original edge support, so it cannot introduce an uncharged expensive edge.
It proves finite attainment, triangle inequalities, exact deletion semantics
and the threshold/all-path equivalence, including loops, unreachable pairs
and zero weights. Edge/vertex gadget reductions remain separate.

`DirectedFlowCutGap.DyadicEdgeWeights` constructs a finite label set of exactly
log₂n+3 labels. Light weights drop to zero, heavy weights clip at one, and
intermediate weights round upward by at most a factor two. Empty-size and
positive-label bounds are explicit.

`DirectedFlowCutGap.EdgeToVertexReduction` proves the actual Theorem30 gadget:
at most 2n(log₂n+4) vertices, total weight and weighted cost at most four times
the originals, and a factor-four bounded-oracle reduction. Directed path
projection, two-label injectivity, endpoint-safe avoiding-path lift and cut-cost
pullback are proved, including the capped-heavy case.

`DirectedFlowCutGap.VertexToEdgeReduction` proves the actual Theorem31 split
construction with exactly 2n vertices and exact weight/objective preservation.
Finite high connector costs force a returned bounded-cost cut onto split arcs.
The metric bridge states the required distinct-endpoint condition explicitly;
cut transfer and zero/empty cases are proved.

`DirectedFlowCutGap.AdaptiveHighProbability` discharges the hard-regime numeric
conditions from the actual uniform initial state, chooses confidence exponent
three explicitly, and instantiates independent minimum-cost amplification.

`DirectedFlowCutGap.AdaptiveAsymptotic` constructs an actual output law in every
size/threshold regime, with explicit full/empty-cut fallback. For every ε>0,
one constant chosen before all graph and threshold instances bounds expected
cardinality by C n^ε(n/L)^(3/2). Independent repetition gives n^(-κ) size-failure
probability while every supported cut is valid.

`DirectedFlowCutGap.AdaptiveVertexBound` composes the actual uniform-weight,
unit-cost and heavy-vertex reductions through bounded-instance oracles. It
proves both all-cost vertex rounding estimates K n^(1/3+ε) and K n^ε sqrt(W),
with K selected before every graph, weight and cost instance. Empty graphs,
zero mass and zero costs are included. These are proved mathematical rounding
bounds; constructive polynomial execution is still being formalized.

`DirectedFlowCutGap.BoundedSampling` removes minimum-positive-weight dependence
from the corrected finite sampler using the original cost oracle. For m>0
items and α>0, the actual admissible family has
T=ceil(2m log(4αmW+m))+1 and inclusion marginals at most 8αw. A proved penalty
argument excludes tiny weights; artificially raised weights appear only in
the potential analysis. For vertex cuts m=n. This result alone gives an
item-count horizon for edges, not a linear-in-vertices edge horizon.

`DirectedFlowCutGap.EdgeRounding` provides the actual-edge all-cost rounding
interface and a real-cost oracle conversion that masks nonedges correctly.
`AdaptiveEdgeBound` applies the dyadic gadget to the vertex bounds, absorbs its
logarithmic size overhead with explicit exponent slack, and proves both main
uniform edge rounding estimates. Each constant is fixed before every graph,
weight and cost instance.

`DirectedFlowCutGap.EdgeFlow` identifies the finite incidence program with
actual edge loads and edge objectives. It constructs attained maximum sum-edge
multiflow and minimum fractional edge cut with equal objective. Zero capacities,
unreachable demands and irrelevant nonedge costs are covered; diagonal demands
are explicitly excluded by fractional feasibility.

`CandidateGridRounding`, `CandidatePotentialSoundness` and
`CandidateGridOptimizer` prove exact finite-grid optimization for bounded integer
difference constraints and then for the actual endpoint-safe candidate problem.
Common-shift rounding handles signed objectives; clipped actual port distances
supply completeness; caps apply only outside the current cut. The single-pair
and finite-family results compare against every real feasible candidate.
They establish integrality and exact optimum existence, not a polynomial-time
optimizer or an executable replacement for the earlier classical selection.

`FiniteHarmonicThreshold` and the four `SparsestVertex/EdgeBridge/Corollary`
modules prove actual distance scaling, positive separated-demand counts and
uniform sparsity bounds in both models. They use the explicit scale-invariant
parameter W_avg=|P|W/S, where S is the sum of finite demanded distances.
The produced cut has sparsity at most K n^ε min(n^(1/3),sqrt(W_avg)) times
the fractional ratio. When average demanded distance is one, W_avg is exactly
raw W. Unreachable, empty and zero-sum cases are separated. The assignment-level results are now connected to attained normalized optima
and actual concurrent flow by the modules below. See
[the normalization contract](SPARSEST_CUT_NORMALIZATION.md).

`AttainedOptima` and `OptimalFlowCutBounds` construct actual integral minima,
fractional minima and maximum sum-multiflows. One constant per positive ε
simultaneously bounds both edge and vertex optima by both advertised factors.
The W-dependent result uses the mass of the same selected fractional optimum.
Zero objectives are handled without assigning a value to an undefined ratio.

`IntegerPackingCovering`, `ConcurrentProfiles` and `ConcurrentDuality` prove
multiplicity-aware profile packing, its exact product/marginal equivalence with
common-throughput flow, and attained duality with the positive-distance
fractional sparsest ratio. `ConcurrentVertexFlow` and `ConcurrentEdgeFlow`
instantiate actual graph paths and apply the main normalized sparsest bounds
to that same optimizer. Average-distance-one normalization gives λ=C/|P|.
Unreachable, empty, all-free and zero-cost cases are explicit. See
[the concurrent-flow contract](CONCURRENT_DUALITY_CONTRACT.md).

`TinyEdgePreprocessing`, `WeakDecomposition` and `WeakDecompositionBounds`
construct the repaired weak-decomposition PMF, with valid supported cuts and
both uniform marginal bounds. Dropping tiny edge weights and doubling the
others gives an exact horizon ceil(2n log(n(2W/Δ+n)))+1. The general reduction
states its modified-weight oracle contract explicitly; it assumes no equality
between gap parameters at W and 2W.

`IntegralNetworkFlow`, `IntegralAugmentation` and `IntegralMaxFlow` construct
actual integer flows and capacity/conservation-preserving unit augmentations.
A finite recursion bounded by a separating cut's capacity returns an exact
maximum-flow/minimum-cut certificate. Residual-path search is an explicit
certified parameter; the supplied classical instance proves existence only.

`MinimumClosureProblem`, `CandidateThresholdClosure`,
`CandidatePortDifferenceSystem`, `MinimumClosureCut` and
`MinimumClosureOptimizer` encode integer potentials by actual threshold bits,
including level zero and negative bounds. A finite-barrier network and the
augmentation recursion at the computed sum-of-absolute-cost budget produce an
exact closure optimum. The candidate instance has budget at most 6n(L+1).
No optimal cut is assumed; efficient search and complete adaptive substitution
remain separate.

`IntegerEpochParameters` proves computable natural restart/fuel/cap parameters,
subpolynomial analytical bounds, the coarse cap bound 4n^6, and exact equivalence
when an unweighted threshold is ceiled. It does not assert that the existing
choice-based adaptive law already uses these replacements.

## Source issues and remaining work

[CORRECTIONS.md](CORRECTIONS.md) records three independently checked failures of
printed proof components: endpoint deletion in Lemma 18, lost demands in
Theorem 29's contraction, and Theorem 33's unscaled multiplicative update. They
are not counterexamples to the headline bounds. The original PDF is unchanged.
The checker in `verification/` reproduces the finite examples; it is not a Lean
proof certificate.

The remaining work includes:

- Constructive residual search, shortest paths and exact finite sampling
- Substituting the computed grid optimizer into the actual adaptive law
- Complete operation counts, rational encodings and polynomial LP computation
- Full-paper statement, build, axiom, kernel and independent semantic audit gates

The [statement map](STATEMENT_MAP.md) separates completed finite components from
each numbered result. The source inventory contains all 33 numbered results,
three definitions and two algorithms. No missing theorem is replaced by a custom axiom or `sorry`.

## Verification

Lean 4.34.0 and the repository's pinned mathlib revision are unchanged.
The seventy-one source modules have warning-free compilation receipts with
`autoImplicit=false`; the current aggregate also passes `warningAsError=true`.
All 3485 distinct declarations pass a fresh allowed-axiom audit. Each component
has an isolated official kernel replay: unchanged exact-source receipts are
inherited for the baseline 52, and all 19 additions have fresh receipts. The
aggregate was also replayed separately. This incremental coverage, source and
dependency hashes, and exact ownership are recorded in
[the verification summary](VERIFICATION.md).
A root replay is distinct from replaying every imported module. Full final-paper
verification and runtime completion remain pending.

Run from the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
python "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/check_counterexamples.py"
```

Pinned PDF SHA-256:
`a0f6f3a73acbfbb1c82fe04d739283c87b3e34d7f6ff850543dcb42b702c3a46`.
Pinned TeX archive SHA-256:
`9d76894e97711df52b099d4f77061c7b5737a86958fc67d2f981b1be1680ce9e`.
