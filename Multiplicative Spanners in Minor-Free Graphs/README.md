# Multiplicative Spanners in Minor-Free Graphs

Greg Bodwin, Gary Hoppenworth and Zihan Tan.
[Source paper, arXiv:2504.16463v1](https://arxiv.org/abs/2504.16463v1).

**In progress.** Actual sparsity has full exact-commit CI. Weighted lightness,
runtime and the final whole-paper audit remain open.

## Current verification state

Latest full terminal checkpoint: 356 modules, commit `9de7b312c6b3214d2b106f0392b78e3f90a89ae4`, with
[full CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38220312555)
passing all eight stages, 500 exact-tree repository replays and 2,184 own declarations.
The 373 parent is published at `96d735df` with
[full CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38229961002)
recorded separately. Earlier 284 and 306 runs reached confirmed 60-minute replay
caps; their exact logs and annotations are preserved. The reviewed 90-minute cap
and every gate remain unchanged in this candidate.

The actual short-simple-path components are constructed and partially absorbed through their genuine boundary owners. Long components remain whole with genuine long spanning paths. Actual original residual degrees pay absorbed-label edges; expanded weak roots retain touching bills while expanded high roots retain marked bills. Literal original unordered edge bags, every unabsorbed old credit and the same root metric/future credits share one ledger. The old selected-root and new mixed connector pools are proved disjoint and their exact union is retained.

“Short” bounds maximum simple-path mass, not total component mass. The
construction allows a branching short component to have large total mass.
The final theorem constructs the actual short family and boundary owners,
while its preceding phase certificate and parameter compatibility stay explicit.

The prior four-phase certificate, common-tree maximality and individual reserve/scale inequalities remain explicit inputs. Their joint actual-selection instantiation, expanded-family reindexing for the later long-component phase, empty-root handling, compatible numerical and asymptotic scales, global weighted lightness, runtime and final whole-paper audit remain open.

All eight new strict builds, 381-module root/index, exhaustive 2,305-declaration
permitted-axiom audit, eight official kernel replays and independent exact-source
review pass. All 373 inherited proof bodies and every workflow/checker remain
unchanged. Full exact-commit CI follows publication.
See the [review brief](verification/PARTIAL-SMALL-REVIEW-BRIEF.md).
The owner-private PaperLab retains the original article and all seven boxed-L
notes. Its deployment receipt separately records the displayed CI snapshot.

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

## Historical component log

The sections below record earlier checkpoints and their then-open gaps.
Their historical status sentences are superseded by the current verification
state above and `verification/status.json`; their mathematical sources remain
byte-for-byte preserved.

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

The actual cluster hierarchy and BLWN17 lightness charging argument remain
open. The new 185 proof supplies the density witness and sparsity upper, with
full exact-commit CI still separate. See
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

## Next finite swap-accounting checkpoint

Six further modules, now through all local gates and fresh component review,
prove actual selected-fiber collision budgets, mated-star incidence bounds,
unique-leaf partitioning of unmated bad neighbors, and exact ordered
forest-edge witnesses for the bad-pair score. Removing one forest edge
loses two ordered witnesses per bad neighboring star through that leaf.
An internally constructed minimum family therefore creates at least that
many new witnesses under each actual admissible unmated exchange. The
local newly-bad-pair classification charges its exceptional third centers
to actual common neighbors of old leaves and connects badness to a real
simple-quotient fiber of size two. The upper bound on all newly created
witnesses and the quantitative cleaning theorem are still open.

## Actual induced dense-witness continuation (100-module candidate)

Six new modules classify every newly created ordered forest-edge witness,
including pairs of centers that remain bad but change their unique leaves.
They transport the literal swapped branches into the actual induced graph
H on the union of stars meeting N(u) or N(b), and inject both inserted-edge
witness classes into real neighbor sets inside H. The exceptional classes
are charged to original-host common neighbors, retaining all mate-free
premises. The finite minimum is constructed internally.

For M actual unmated bad partners sharing a forest edge b-u, the endpoint
constructs the real induced H with
`|V(H)| <= (ell+1)*(degree_G(u)+degree_G(b))` and
`M*(M-2*ell*q) <= 2*|E(H)|`.
The partner centers and leaves are disjoint actual vertex injections, so
handshaking supplies the latter inequality. The stronger
`M^2 <= 4*|E(H)|` explicitly requires `M >= 4*ell*q`.
The statement handles q>=0 and preserves the exact covered-leaf set.

This does not infer absence of H from literal Unmated, prove the remaining
residual-fiber allocation, or certify quantitative cleaning, a density
increment, or either main upper spanner bound. A prospective threshold
r>=4*ell*q requires epsilon2<=epsilon1/(4*ell) when r=epsilon1*d,
q=epsilon2*d and d>0. The comparison with global inverse-k scales does not establish a polynomial
change for the paper's separate bipartite application: Postle Theorem3.6
uses eps1,0=1/ell andeps2,0=1/ell². For that domain, the displayed relation
requires a constant-factor reduction in eps2,0. No final asymptotic repair
is claimed without the remaining graph and iteration joins.


## Quantitative incidence and all-fiber accounting (107-module candidate)

The next seven modules retain a genuine small dense induced subgraph as
an alternative, with vertex count at most2(ell+1)D and4|E(H)| at least r².
Otherwise an internally selected full mate-free family has every actual
unmated leaf-incidence class smaller than r. The relation4ellq<=r and the
upper degree D on every original selected center and covered leaf are
explicit. Literal Unmated does not silently rule out the dense witness.

Actual mated-center and unique-leaf counts bound the complete ordered
bad-pair score. The graph join assumes q=eps2*d, D<=K*d and literal Unmated,
and proves the quantitative selected-star surplus estimate. General branch
fibers identify real unordered host edges between the covering branches.
Every residual vertex is retained as a singleton. Mixed fibers are paid by
actual leaf-collision counts, while residual/residual fibers lose no edge.
The complete ordered-fiber sum is at most four times the total directed
collision count plus the ordered bad-pair score; both orientations and all
four branch categories are included. A generic actual-edge-set inequality
relates unordered quotient costs to the ordered-pair sum.

The additional exact host-edge identity wrapper is outside this frozen
batch while its finite-enumeration elaboration is repaired. No completed
regularization-to-density-increment assembly or main upper theorem is
claimed. The parameter relation is substantive: when r=eps1*d,q=eps2*d,
it requires eps2<=eps1/(4ell) for d>0 and ell>0. All downstream parameter
losses and asymptotic joins remain separate proof obligations.

## Actual clean covering-minor alternative (109-module candidate)

FullStarEdgeBudget joins the full actual quotient edge-loss identity to the
ordered-fiber bound, including every residual vertex and every simple edge.
CleanStarContraction internally selects a valid minimum family with the same
centers and covered leaves. It either produces an actual induced H with
|H| <= 2(ell+1)D and r² <= 4|E(H)|, or supplies a genuine covering minor Q,
width at most ell+1, all original-host mate-free branches, the exact identity
|V(Q)|+ell|C|=|V(G)|, and
|E(G)| <= |E(Q)| + [ell+4ell(ell-1)q+(ell+1)eps1*d+ell*r]|C|.
The collision product ell(ell-1) remains natural-number arithmetic.

The theorem assumes an actual bipartite host, C contained in its right side,
a supplied full mate-free initial star family, an upper degree D for every
center and covered leaf, D<=K*d, literal Unmated, q=eps2*d>=0, and4ellq<=r.
It does not assume a cleaning conclusion, a minimum oracle or a quotient-loss
bound. Constructing and regularizing the initial family in the exact parameter
regime, then joining the density increment and main upper bounds, remains open.

## Scaled cleaning and actual selected-host regularization (114-module candidate)

CleaningScales and ScaledCleanContraction prove one explicit conservative
parameter domain: k>0,1<=ell,4ell<=k,d>=k²,eps1=1/(100k²),eps2=1/(100k³),
K=5k. Under the actual initial-family/degree hypotheses, an induced H has
|H|<=10k²d, positive edge witness (d/(100k²))²<=4|E(H)|, and density at least
d/(400000k⁶), or a real full covering mate-free minor loses at most
2ell*d/k² per selected center. The positive edge bound is retained, so the
empty graph cannot make the dense alternative vacuous.

SelectedStarHost proves exact induced degree plus actual boundary count
is the original leaf degree. InducedStarFamily constructs the literal
selected-vertex subtype, its full star assignment, exact left/right size
ratio and bipartition. A genuine common-neighbor injection preserves
mate-freeness. SelectedStarRegularization internally chooses a graph between
that forest and its induced host with exact left degree m and edge count
m*|A'|, preserving every star edge, full coverage and the mate threshold.
Its integer premise1<=m<=(1-eps)*d is explicit. Global Unmated is not treated
as hereditary under this deletion; a later small-dense alternative is needed.

This conservative parameterization is not asserted to be the only valid
route. Postle Theorem3.6 has distinct bipartite epsilon parameters from
Theorem3.7, and its application uses inverse-ell/inverse-ell² scales. The
separate inverse-quadratic draft is outside this freeze/review. Neither
this checkpoint nor that draft completes the full density increment,
asymptotic parameter iteration, or main upper spanner/charging argument.

## Actual regular bipartite density minor (123-module candidate)

The nine new modules use the separate inverse-quadratic bipartite domain:
k>0, 1<=ell, 4ell<=k, d>=k, K=5k², eps1=1/(100k), eps2=1/(100k²).
From an actual finite bipartite regular host with nonempty right side B,
|A|=ell|B|, left degree m satisfying (1-1/(100k))*d<=m<=d, literal Unmated,
and a supplied full mate-free star family centered on B, the final theorem
internally constructs the low-degree center subset and its retained-count
bound. It then quantitatively cleans and removes only actual uncovered
singleton left branches from the simple quotient.

The result is either an actual induced H with |H|<=10k³d,
(d/(100k))²<=4|E(H)| and density at least d/(400000k⁵), or a genuine
width-(ell+1) minor Q with positive vertex count exactly |B| and
|E(Q)| >= (ell-1)*d*|B|. The deleted-label bijection, singleton degree loss,
all quotient fibers, exact regular-degree cancellation, floor bound and
retained-center count are proved on concrete finite objects. The initial
full family and literal Unmated premise remain explicit.

Constructing this regular host from the original graph, reapplying the
small-dense alternative after actual edge deletion, and lifting its result
remain the next join. Global density iteration and the main upper spanner
and charging results remain open. The current fully certified checkpoint
is 114 modules at cc97a09e; its full CI succeeded 11 October 2026. The
private PaperLab v19 pins that certified revision.
