# Multiplicative Spanners in Minor-Free Graphs

Greg Bodwin, Gary Hoppenworth and Zihan Tan.
[Source paper, arXiv:2504.16463v1](https://arxiv.org/abs/2504.16463v1).

**In progress. The conditional fixed-k lower bounds for sparsity and genuine
connected-graph lightness are proved locally. The main upper bounds remain open.** This checkpoint starts the actual graph proofs and records
three source corrections without silently changing the paper.

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
Current25 modules/257 declarations pass local build, index, axiom audit and
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

## Remaining work

The density-increment theorem, the h=3 normalization boundary, actual cluster
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
