# Improved Upper Bounds for the Directed Flow-Cut Gap

Greg Bodwin and Luba Samborska · FOCS 2026 · [arXiv:2604.03412v3](https://arxiv.org/abs/2604.03412v3)

**Partial formalization. The main flow-cut bounds are not yet proved.**
This checkpoint preserves twenty-eight completed components and reproducible checks of
three source-proof issues. It does not certify the whole paper or all advertised
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

## Source issues and remaining work

[CORRECTIONS.md](CORRECTIONS.md) records three independently checked failures of
printed proof components: endpoint deletion in Lemma 18, lost demands in
Theorem 29's contraction, and Theorem 33's unscaled multiplicative update. They
are not counterexamples to the headline bounds. The original PDF is unchanged.
The checker in `verification/` reproduces the finite examples; it is not a Lean
proof certificate.

The remaining work includes:

- Complete adaptive epoch process and the remaining edge/vertex reduction network
- Full candidate/level-cut iteration, probability laws, stopped epochs and charging
- Apply the proved stable-state graph-value bound to the adaptive stopping/cost proof
- Edge/vertex transformations and final asymptotic composition of the finite reductions
- Uniform n^(1/3+ε) and n^ε sqrt(W) bounds, with constants independent of weights
- Sparsest-cut and weak-decomposition corollaries and their necessary bridges
- Rational encodings, probability guarantees and algorithmic complexity
- Full-paper statement, build, axiom, kernel and independent semantic audit gates

The [statement map](STATEMENT_MAP.md) separates completed finite components from
each numbered result. The source inventory contains all 33 numbered results,
three definitions and two algorithms. No missing theorem is replaced by a custom axiom or `sorry`.

## Verification

Lean 4.34.0 and the repository's pinned mathlib revision are unchanged.
The twenty-eight source modules and aggregate compile with `autoImplicit=false`.
All 1770 declarations pass the allowed-axiom audit, and all twenty-eight components plus
the aggregate pass official separate kernel replay. Evidence is recorded in `verification/`. These are component
checks, not a full-paper release.

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
