# Multiplicative Spanners in Minor-Free Graphs

Greg Bodwin, Gary Hoppenworth and Zihan Tan.
[Source paper, arXiv:2504.16463v1](https://arxiv.org/abs/2504.16463v1).

**In progress. The conditional fixed-k lower bounds for sparsity and genuine
connected-graph lightness have full exact-commit CI. The main upper bounds remain open.** This checkpoint constructs actual graph proofs and records
three source corrections without silently changing the paper.

## Current verification state

The 75-module checkpoint `c85035864ef07e968bb204d838fe2c42837b4eb4`
passed full [exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38089280046),
including every project kernel replay, on 10 October 2026 at 22:27 UTC.
All 713 own declarations pass the permitted-axiom audit, and all eleven
hash-pinned component reviews pass. Owner-private PaperLab v12 is pinned
to that certified revision, including actual mate-free star selection and
full covering simple contraction with residual singleton branches.

The 84-module accounting checkpoint `2e34a2da84685016aaa5085b261107c1caee6094`
is published with all strict source/root/index checks, 774-declaration axiom
audit, independent kernel replays and twelve exact-source component reviews
passed. Its [exact CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38091432747)
is running separately. Quantitative cleaning and the main upper bounds remain open.
See `verification/status.json` for the separate evidence levels.

## Scope

- Finite simple undirected graphs and actual mathlib walks.
- Explicit branch-set minor models: nonempty, pairwise disjoint connected
  vertex sets, with an actual host edge for every model adjacency.
- Actual sorted-edge greedy construction, with ties handled by its order.
- Positive real edge weights for girth interpretation; nonnegative weights
  suffice for stretch. ENNReal shortest distances handle disconnected pairs.
- Paper Claim 19 is replaced by the exact `t+1` weighted-girth guarantee.
  A parameterized actual greedy triangle refutes the printed threshold,
  including arbitrarily small positive `sε`; the numerical repair uses
  `s≥4g`. See [CORRECTIONS.md](CORRECTIONS.md).

## Proof modules

- `Minor`: branch-set model, hereditary clique-minor exclusion, cardinality
  obstruction, singleton-branch embedding.
- `Greedy`: Claims 14, 15, 18; corrected Claim 19; shortest-distance bound;
  exact scalar repair needed by Claim 23.
- `Claim19Counterexample`: actual greedy triangle family; metric-edge and
  K₄-minor-free hypotheses checked explicitly.
- `SmallMinors`: K₂-minor-free graphs are exactly edgeless graphs, clarifying
  the bounded-h lower-bound domain.
- `LowerBound`: every `(2k−1)`-spanner of an unweighted girth-`>2k` graph is
  the entire graph. This is the edge-forcing step, not the full lower bound.
- `Moore`: Theorem 11, with the explicit uniform constant2 and exact power
  form, reusing the repository's proved graph-level Moore theorem.
- `MinorEdgeCount`: a branch-set minor has at most as many edges as its host;
  fewer than `h.choose 2` host edges exclude a Kₕ minor.
- `DensityAlgebra`: eliminates the witness size and extracts the exponent
  `2/(k+1)` with all constants explicit. The small dense witness is not
  assumed to exist in a completed graph theorem.

The precise verification state is in [verification/status.json](verification/status.json).
[The source inventory](verification/source-inventory.json) accounts for all
25 unique numbered items, including cited background and conjectures.

## New graph components in this checkpoint

- `MinorComposition`: constructs walk lifts and genuine composite minor models.
- `MinorRestriction`: injective host transport, induced restriction and
  reduction to actual connected components; componentwise edge obstruction.
- `GirthComponents`: injective cycle transport and componentwise girth.
- `DisjointCopies`: an explicit graph on `J × V`, with exact vertex and
  edge multiplicities, minor/girth preservation and spanner edge forcing.
  This is the finite core-copy step, not a complete asymptotic lower bound.
- `MinorSingletonDegree`: singleton branch degree cannot exceed host degree.
- `SubdivisionMinor`: the actual one-edge `LightSpanners.subdivideEdge`
  preserves clique-minor exclusion for `h ≥ 4`. Walks are contracted with
  support control; model branches and crossing edges are built explicitly.
  The next component carries this through full normalization for h≥4; small-h completion remains separate.
- `DensityLinearLoss`: the arithmetic bound has uniform coefficient 2 and
  linear density loss L. Existence of the dense witness remains open.

The 15-module checkpoint 8954f54 has full exact-commit CI success. Its audit
covers 151 declarations, and every new
module plus the unchanged borrowed subdivision module passed local kernel
replay. The initial eight-module checkpoint has independent semantic review
and full exact-commit CI success. The seven additions have a separate
component review and exact-commit CI gate, recorded in the status file.
The initial source manifest is `verification/source-hashes.json`; the
15-module source manifest is `verification/checkpoint2-source-hashes.json`.

## Third component batch

- `MinorNormalization`: actual terminating repeated subdivisions carry the
  minor invariant; scaling and rounding produce an actual unit-weight MST,
  at most `2n−1` vertices and at least half the original lightness. Domains:
  `h≥4`, `n≥2`, nonnegative girth parameter, positive graph-edge weights,
  and an actual input MST. No nonforest premise is needed.
- `IsolatedPadding`: adjoining isolated vertices preserves edge count,
  cycle girth and clique-minor exclusion for `h≥2`.
- `ExactSizeLowerBound`: exactly `n` vertices, using floor(`n/v`) copies and
  remainder padding; every `(2k−1)`-spanner retains the entire graph and
  `n*m_core ≤ 2*v_core*m_output`. A dense high-girth core must still be
  constructed from the paper's explicit conjecture. This is sparsity only.
- `IntrinsicGirthGap`: actual alternative walks avoiding an edge have weight
  greater than `(g−1)` times that edge under weighted girth `>g`.
- `ClusterGraph`: an actual cluster quotient minor, no heavy intracluster
  edge, and uniqueness of heavy intercluster edges under explicit diameter
  and weight budgets. Equal weights are allowed; no preserved greedy order
  is assumed after normalization. The fourth batch proves cycle lifting;
  hierarchy existence remains open.

All 20 modules compile and all 216 declarations pass the allowed-axiom audit.
The current source manifest is `verification/checkpoint3-source-hashes.json`.
Kernel replay, bounded semantic review and exact-commit CI are recorded
separately in the status file; this is not a complete main-theorem proof.

## Fourth component batch: actual Claim23 cycle lifting

- `ClusterEdgeWeights` selects symmetric coarse-edge weights from real host
  bridges and proves a realizing bridge exists in either orientation.
- `CycleEdgeRemoval` removes a chosen edge from an actual closed trail,
  preserving all other edges and the exact length decrement.
- `ClusterWalkLift` constructs a host walk with a checked weight budget and
  avoidance of a designated edge.
- `ClusterGirth` combines these constructions with intrinsic weighted girth
  to prove actual quotient girth, with explicit diameter/weight budgets.
- `ClusterClaim23` proves clique-minor exclusion and girth `>2k` for an actual
  supplied cluster family, using corrected Claim19 and `s≥4g`.

The hierarchy must still be constructed, and its edges still need a charging
proof. No cycle oracle or preserved greedy order is supplied as a hypothesis.
The 25-module checkpoint passed local build, index, axiom audit and
kernel replay. The hash-pinned review and exact-commit CI are separate gates.

## Fifth component batch: the complete conditional sparsity family

- `CoreExtraction`: deletes an actual finite edge subset to attain an exact
  edge count while preserving girth.
- `CoreParameters`: proves explicit floor/ceiling bounds for a core with
  `v = ceil(h^(2k/(k+1)))`, `m = floor(a h²)`, and `m < choose(h,2)`.
- `GirthConjectureLowerBound`: constructs the required core from the genuine
  fixed-k Erdős girth conjecture, then joins exact-size copies and padding.
- `StarLowerBound`: proves actual stars exclude every Kₕ minor for h≥3 and
  force every spanner to retain all n−1 edges.
- `AllCliqueOrdersLowerBound`: joins the large-h family and bounded-h stars.

The final theorem `girth_conjecture_sparse_lower_bound_all_h` states that,
for each fixed k≥1, Conjecture12 implies the existence of c>0 such that
for every h≥3 and every sufficiently large n, there is an actual n-vertex
Kₕ-minor-free graph whose every unit-weight (2k−1)-spanner has at least
`c n h^(2/(k+1))` edges. The constant may depend on k, but is uniform in h
and n; the n threshold may depend on h and k. The only unproved mathematical
premise is the source's explicitly conjectural high-girth graph family.
The sixth batch supplies an actual connected construction and input MST. Local gates,
component review and exact-commit CI remain separately recorded.

## Sixth component batch: connected lightness with a genuine MST

- `RootedCompletion` adds one hub and one edge per actual old connected
  component. It proves connectivity, that every new edge is a bridge, and
  preservation of all cycle-girth lower bounds.
- `MinorWeakMap` maps genuine walks and minor models through explicit edge
  collapses, requiring and proving branch-image disjointness at use sites.
- `LeafMinor` proves pendant-vertex additions preserve Kₕ-minor exclusion
  for h≥3, including the old-vertex and degree arguments for each branch.
- `CompletionMinor` localizes clique models to one old component plus a
  pendant hub and proves the connected augmentation remains Kₕ-minor-free.
- `ConnectedLowerBound` constructs an actual unit-weight MST and proves the
  final simultaneous sparsity and lightness family on exactly n vertices.

`girth_conjecture_connected_lower_bound` states: for fixed k≥1, Conjecture12
implies ∃c>0, ∀h≥3, for every sufficiently large n there is a connected
n-vertex Kₕ-minor-free unit-weight graph G with an actual MST T such that
every (2k−1)-spanner J has at least `c n h^(2/(k+1))` edges and actual
lightness `totalWeight J / totalWeight T ≥ c h^(2/(k+1))`. The denominator
is n−1>0; it is never an MST of a disconnected graph. Constants are uniform
in h,n for fixed k. No claim of unconditional proof of the girth conjecture
is made. See the status file for distinct local, review and exact-CI gates.

## Seventh component batch: normalization and Postle graph foundations

- `TriangleMinor`: constructs an actual K₃ branch-set model from any cycle,
  proving that K₃-minor-free graphs are forests.
- `ThreeMinorNormalization`: closes h=3 via the actual input tree/MST;
  the combined normalization theorem covers every h≥3, with at most 2n−1
  vertices and at least half the original lightness.
- `BoundedMinor`: actual bounded branch-set composition, target restriction,
  and dense induced-subgraph pullback with vertex and edge bounds.
- `PostleBudget`: source-checked real-parameter rounding boundaries.
- `PostleMates`: the actual induced-neighborhood graph and common-neighbor
  degree-sum argument prove Postle Proposition3.2 throughout K,d≥1.
- `PostlePullback`: actual bounded-minor Corollary3.3, for integer widths.
- `PostleParameterBudget`: actual later parameter inequalities and corrected
  coefficient identity, without an assumed density-increment theorem.

The redundant v is omitted from N(v) union selected mates, preserving all
required incidences while retaining the original 3Kd bound throughout the
printed real domain. The external proof arithmetic notes do not refute any
proposition or main theorem. The full density-increment construction remains
open. See separate focused checks, aggregate gates, reviews and CI status.

## Remaining work

The density-increment theorem, actual cluster
hierarchy and BLWN17 charging argument remain open. See
[DEPENDENCIES.md](DEPENDENCIES.md). None is disguised as an axiom, supplied
oracle, or hidden premise of a purported completed main result.

## Checks

From the repository root:

```sh
lake build MinorFreeSpanners
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

Local compilation, all-declaration axiom audit, independent kernel replay,
independent semantic review and exact-commit CI are separate gates. A fresh
skeptical final audit is additionally required on completion before a link
is added alongside the paper on Greg's research website.

## Actual contractions and minor-minimal dense neighborhoods

The next eight modules add proved graph constructions, without assuming a
clique-minor threshold or the density-increment theorem:

- `PostleBipartiteTrim`: choose an actual subgraph with exactly m neighbors
  at each left vertex; its edge count is m times the left-side order.
- `PostleSubgraphUnmated`: reapply the proved small-dense/unmated alternative
  after edge deletion. Global unmatedness is not asserted to be hereditary.
- `MateFreeSets`: actual common-neighbor monotonicity, pairwise mate-free
  sets, and bipartite star-center extension.
- `EdgeContraction` and `EdgeContractionCount`: remove one endpoint and
  merge its adjacencies in an actual simple graph. The genuine width-two
  minor model, exact one-vertex loss, and exact edge loss
  `1 + card(commonNeighbors u v)` are proved. Loops and parallel edges are
  explicitly suppressed.
- `MinimalDenseMinor`: select an actual nonempty finite minor minimizing
  vertices plus edges. Integer density d is explicit. Actual edge trimming
  proves `E=dN`; smaller actual minors have density below d.
- `DenseMinorNeighborhood`: contraction forces at least d common neighbors
  on every edge of that minimal graph. An actual induced neighborhood is
  then a genuine host minor, is nonempty, has at most 2d vertices and has
  minimum degree at least d. The input is any nonempty finite host with
  integer d>0 and at least d times its order in edges.
- `RobustCommonNeighbors`: explicit two-hop walks survive any deletion set
  smaller than the common-neighbor bound. This is actual preconnectedness,
  not a supplied connectivity certificate.

The neighborhood argument formalizes the deterministic opening of
Alon–Krivelevich–Sudakov, [Complete minors and average degree — a short proof](https://www.math.tau.ac.il/~krivelev/KT-minors.pdf),
page 2. Their sharp clique-minor theorem is not proved here. The following
component instead constructs a weaker O(h log h) threshold through actual
separators, connected dominating sets and branch-set iteration. The separate
small-dense-subgraph increment and main spanner upper bounds remain open.

## Actual logarithmic clique-threshold construction

The fourteen-module candidate constructs a genuine complete minor whenever
`h > 0`, the host is nonempty, and
`|E(G)| ≥ 24576 * h * (Nat.log 2 h + 2) * |V(G)|`.
Its excluded-minor edge corollary also covers empty hosts. Here `Nat.log 2` is the base-2 logarithm with floor rounding; all constants
are explicit.

- `InducedDegreeBudget`, `FiniteSeparatedSide`, `RobustSubgraph`: actual
  separator-side extraction, induced degree loss and deletion robustness.
- `DenseGraphDiameter`: an actual shortest-walk argument with five disjoint
  open neighborhoods gives a walk of length at most 11.
- `GreedyNeighborhoodCover`, `GreedyDominatingSet`: finite incidence counting
  and an actual iteration construct an open-neighborhood dominating set of
  size at most `4*(Nat.log 2 n+1)`.
- `ConnectFiniteSet`, `SmallConnectedCover`: unions of actual short walks
  connect the selected vertices, with at most `48*(Nat.log 2 n+1)` vertices.
- `RobustCoreDeletion`, `ResidualConnectedCover`: actual nonempty surviving
  induced graphs and mapped connected branches avoid every small prior deletion.
- `ExtendCliqueModel`, `RobustCliqueConstruction`: finite induction builds
  disjoint connected branch sets and every required actual crossing edge.
- `CliqueDensityBudget`, `LogarithmicCliqueThreshold`: explicit integer
  rounding/power budgets and the actual host-graph minor/edge-count theorem.

This is an elementary `O(h log h)` threshold, not the sharper cited
Kostochka–Thomason `O(h sqrt(log h))` bound. It is sufficient as the global
minor-density threshold within the paper's unspecified polylogarithmic
loss, but **does not supply Postle's separate small-dense-subgraph increment**.
That increment, the cluster hierarchy and lightness charging remain open.
No density, diameter, connected-cover or complete-minor oracle is assumed
by the new endpoint. Prior fifty proof sources are byte-identical.

## Actual full-star selection and bounded quotient

The new seven-module candidate constructs the star family used in Postle's
Lemma 4.1 (source PDF page 9), without a packing or augmentation oracle:

- `FiniteStarPacking`: select a maximum actual finite leaf assignment;
  insert a genuinely unused compatible leaf into a star with spare capacity.
- `StarPathAugmentation`: construct every edge exchange, preserve actual
  independent disjoint leaves, convert original-packing routes to the
  dynamically reassigned packing, and prove an exact one-leaf gain.
- `SimpleRelationPath`: erase repeated vertices from arbitrary directed
  relation reachability while preserving both endpoints and every step.
- `StarCenterReachability`: construct the static alternating route from a
  simple center chain; maximum size forces every reachable center full.
- `StarConflictCount`: inject blocked centers into distinct actual neighboring
  leaves. This constructs a compatible seed and bounds the outside boundary.
- `StarPackingSelection`: internally choose the maximum, handle complete
  coverage and uncovered leaves, and return actual full stars.
- `StarPackingMinor`: prove disjoint induced-star branches, actual internal
  walks of length at most two, exact selected-vertex count, and a genuine
  width-`ell+1` simple quotient minor.

The endpoint `exists_full_star_minor` assumes disjoint finite domains A,B,
`ell*|B| <= |A|`, and integers `dA<dB`, with each A vertex having at most dA
actual neighbors in A and at least dB in B. It constructs C contained in B,
exactly ell independent leaves at each center, and at most dA neighbors in
B\C for each selected leaf. C is nonempty when A is nonempty, and the literal
star union has `(ell+1)*|C|` vertices. Ordinary claws use ell>=1; the generalized
core also handles ell=0 as singleton branches. The source's additional
partition and B-independence conditions imply these hypotheses.

A separate forest-valued packaging of F is not supplied by this endpoint.
The quotient here retains selected centers only; unselected host vertices
are deleted. The next batch supplies a full contraction retaining their singleton
branches and actual mate-free selection. Its edge-loss budget, clean
contractions, the density increment and the main spanner upper bounds remain open.


## Mate-free selection and full covering contraction

The four new modules provide the regularized/small-left application of
Postle Lemma 4.2, followed by an actual quotient of the entire vertex set:

- `MateAugmentation`: add literal distinct mate pairs inside A, bound the
  resulting internal neighbor count, and transfer independent stars back to
  the original graph with genuine common-neighbor mate-free branches.
- `MateFreeStarSelection`: construct all stars internally using the previous
  finite augmentation theorem. The real unmated specialization explicitly
  requires every left vertex to have degree at most K*d; a lower degree
  bound alone is never used to infer this upper bound.
- `FullStarContraction`: selected stars become branches and every residual
  vertex remains a singleton. The actual SimpleGraph suppresses loops and
  merges parallel edges. Every host vertex is covered, all branches are
  connected and disjoint, and the exact vertex identity is
  `|V(quotient)| + ell*|C| = |V(host)|`.
- `MateFreeStarContraction`: join the actual choices, covering minor model,
  width `ell+1`, mate-free branches and selected-leaf boundary budget.

The endpoint assumes a finite bipartite graph, natural d>0, 0<=eps1<1,
eps2>0, `ell*|B|<=|A|`, left minimum degree d and the explicit small-left
upper bound K*d. Its `Unmated` premise is the existing literal finite-count
predicate; the already proved dense-subgraph alternative supplies that
predicate separately. It is not advertised as the printed minimum-only
Lemma 4.2 without the additional small-left domain. This batch proves no
cleaning, edge-loss or density-preservation bound.


## Actual regularization and contraction accounting

The next nine-module batch advances the concrete graph proof without
assuming a cleaning bound:

- `RegularStarReduction` internally constructs the exact-left-degree
  subgraph, reapplies the actual small-dense/unmated dichotomy, and constructs
  the mate-free covering minor. Its mate-freeness refers to that subgraph;
  it does not assert hereditary unmatedness or unchanged original-host mates.
- `SimpleQuotientCount` proves exact edge-image, internal-edge and crossing
  fiber identities for the genuine simple graph map under any vertex map.
- `FullStarEdgeAccounting` identifies the actual covering star labels and
  proves that contraction removes exactly ell edges per selected star plus
  the explicit sum of excess crossing-fiber edges. No cleaning estimate is
  hidden inside this exact identity.
- `SmallStarRestriction` deletes degree-large centers from a supplied full
  star cover and proves the literal retained-vertex budget by bipartite
  degree sums. Every retained branch vertex is small in the same host.
- `StarCrossingPairs` and `StarCrossingFiber` identify actual crossing host
  edges and selected-star quotient fibers. Their cardinality is the sum of
  the two directed crossing-leaf counts.
- `MinimumBadStarFamily` internally chooses an actual minimizing assignment
  while preserving fullness, exact covered leaves and original-host
  mate-freeness. Its score counts ordered bad center pairs.
- `CommonNeighborIncidences` double-counts real ordered distinct leaf pairs
  and common-neighbor witnesses, obtaining the corresponding mate-free budget.
- `CrossingSurplusBudget` proves the safe ordered-pair surplus inequality
  and numerical absorption when the common-neighbor threshold is at least1.

The global crossing-fiber allocation and quantitative bad-pair estimate
remain open, so this is not a proof of Postle's cleaning lemma, density
increment, or the main spanner upper bounds. A separate concrete two-star
leaf-swap draft is outside this frozen production batch.


## Actual forest and swap continuation

The next four frozen modules bring the candidate to 88 modules and 816 audited
declarations. They construct the concrete two-star leaf exchange under actual
cross-edge and union-mate-freeness premises; package a genuine acyclic
forest-valued subgraph and exact forest edge count; internally regularize
left degrees while preserving every actual forest edge; and bound the
actual union of stars meeting two host neighborhoods. Strict production
builds, root/index/audit and four independent kernel replays pass. A fresh
exact-source review passed; exact-88 CI has not started. The quantitative
unmated bad-pair argument and full cleaning bound remain open.
