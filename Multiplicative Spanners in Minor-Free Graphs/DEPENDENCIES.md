# Mathematical dependencies and completion boundary

This is an in-progress formalization of Bodwin–Hoppenworth–Tan,
*Multiplicative Spanners in Minor-Free Graphs*, arXiv:2504.16463v1.
The fixed-k conditional lower bounds have full exact-commit CI. The 185-source
checkpoint now locally proves and component-reviews the actual sparsity upper
bound, with fresh full CI pending; weighted lightness remains open.

The original reformulated density-increment dependency is now supplied by
`full_density_witness` and `fullDensityLoss_polylog`, through actual finite
minor iteration and host pullback. The proof uses the project's constructive
O(h log h) clique-density cap, sufficient for the claimed polynomial-log loss;
it does not require the sharper cited O(h sqrt(log h)) threshold. The explicit
loss is bounded by a universal constant times(log₂h+2)^9. `GirthMinorFreeUpper`
and `GreedyMinorFreeSparsity` join this to the actual Moore and greedy graphs.
This does not claim identical constants or verification of every intermediate
printed statement in Postle. Earlier source-proof concerns remain separately
recorded, with no theorem refutation inferred. The notes below are historical
dependency descriptions except the still-open hierarchy and charging items.

The193 candidate now constructs the actual high-degree clustering and payment
phase of the BLWN17 hierarchy. It uses conserved pooled credits, avoiding an
unjustified pointwise interpretation of average degree. The original marked
host-edge injection and the actual induced quotient density bound are proved.
Other hierarchy phases, initialization and global weighted charging remain open.

The201 candidate constructs the actual unit-tree initialization. Maximum
connected-core packing and complete residual-component assignment replace a
supplied initial partition; actual disjoint internal edges fund all reserves.
The integer-scale small-tree case is explicit. The later low-degree, absorption
and global weighted charging obligations remain open.

The 217 candidate closes the actual low-degree branching component. The old
covering cluster family and scale/credit inequalities are explicit; residual
forest selection, minimal branching cores and their maximum disjoint family
are constructed. Original heavy incidence and distinct original unit connectors
supply the exact pooled payment. Path-only residuals, absorption and global
weighted charging remain open.

The 227 candidate closes the actual four-arm path component. The old covering
family and numeric scale/credit inequalities are explicit; threshold arms and
the finite maximum disjoint carrier family are constructed. Original heavy
incidence and genuine unit connectors provide payment with a half-baseline
reserve. Same-path short-cycle cases, absorption and global charging remain open.

The242 candidate closes the actual short-cycle phase and joint far-interior
residual exclusion. The numerical scale/credit conditions remain explicit;
actual path trimming, girth surplus and the finite packing are constructed.
Endpoint/small-component absorption, coverage and global charging remain open.

The257 candidate constructs a covering, paid next family for actual small
residual components. Root ownership and critical-path reserves are internal;
original heavy-edge labels and fresh unit identities survive the merge.
The large-path case, unconditional coverage and global charging remain open.

The265 candidate derives actual long-path donor payment: exact-support
segmentation, internally selected attachment blocks, at-most-two-component
critical reserves, actual mass-derived donor credit and original-host unit
connector payment. Unconditional long-path assembly and global charging remain
open. All257 inherited proof bodies are preserved.

The275 candidate constructs actual residual path-family assembly: internally
selected component paths and attachment blocks, bijective donor transport,
exact full partition, and original-host root/large-block payments. Multi-root
and heavy-edge assignment and global lightness remain open. All265 inherited
proof bodies are preserved.

The284 candidate proves actual residual heavy-edge classification and original
host attachment identity. The paths/blocks are constructed internally around
supplied ports; old-label cover and core maximality remain explicit. Multi-root
credit propagation and global lightness remain open. All275 inherited proof
bodies are preserved.

The295 candidate constructs simultaneous actual root assembly and disjoint
credit pooling, then derives actual short-block heavy absorption using an
internally selected at-most-two-block reserve. The final root-budget provenance
join, compatible scales and global lightness remain open. All284 inherited
proof bodies are preserved.

The306 candidate joins actual unpaid-edge owners, previously spent root
allocations and retained inactive path-block credit in one disjoint original
resource pool. The common earlier-phase instantiation, compatible scales and
global potential remain open. All295 inherited proof bodies are preserved.

The 312 candidate joins the actual common root-fiber construction, full
old-label cover, residual exclusion and retained root/large/small allocation
ledgers. Direct total-heavy-edge weight payment, compatible scales and global
potential remain open. All 306 inherited proof bodies are preserved.

The 318 candidate replaces actual residual-heavy-edge allocations with
original host-edge weight while preserving the complete output ledger. It
constructs the common ownership and path assembly internally. Earlier mixed
root transport, scales and global potential remain open. All 312 inherited
proof bodies and all workflow/checker gates are preserved.

## Reused proved foundations

- `LightSpanners.Basic`, `.Greedy`, `.Distance`, `.Girth`, `.Construction`:
  actual mathlib graph walks, positive real edge weights, ENNReal weighted
  distances, sorted-edge greedy output, stretch and weighted girth. Reused
  source files match the existing project byte for byte.
- `VFTSpanners.Moore`: graph-level Moore bound with explicit uniform constant
  2. Its proof includes path counting and dense-core extraction. This is a
  proved import, not an assumed external theorem.
- Lean 4.34.0; mathlib commit
  `5ed2965256430c3649e86755f9576b54eca72435`.

## Dependency status

1. **Density increment, Theorem 9.** A genuine branch-set minor framework
   and the full small-dense-subgraph construction are required. Postle,
   arXiv:2006.14945v3, is the original cited result. Version 4 is a withdrawal
   because of a stronger coloring result, not a retraction of this theorem;
   see the source paper's footnote 3 and Delcourt–Postle,
   arXiv:2108.01633v5, the remark after Theorem 2.2. No density-increment
   axiom or assumed oracle has been introduced. The reformulation also
   needs the actual clique-minor density threshold (Kostochka–Thomason,
   average degree O(h sqrt(log h))): one chooses D at that threshold to
   exclude Postle's dense-minor outcome. This dependency is explicit in
   Delcourt–Postle v5, page 4, between Theorems 2.1 and 2.2. The original
   density-increment theorem uses edge density e(G)/v(G), rather than
   average degree 2e(G)/v(G); the factor of two must be tracked. Its
   constant-density and edgeless boundary cases also require separate
   treatment. None of these external graph theorems is currently proved
   by the density-elimination arithmetic module. `PostleMates` now proves
   Proposition3.2 using an actual induced graph and degree-sum count, and
   `PostlePullback` proves Corollary3.3 for integer-width genuine bounded
   minor models. The new bipartite_density_increment theorem constructs the initial
   regular graph, full mate-free family and actual quotient internally in
   the explicit domain 4ell<=k<=d, natural ell,d. Its dense alternative has
   size at most10k^3*d and density at least d/(400000k^5); its actual
   (ell+1)-bounded minor has density at least(ell-1)*d. The full printed
   parameter range, general-graph Theorem3.7 and global iteration remain
   open. Harmless source arithmetic repairs are
   separately disclosed in CORRECTIONS.md.
2. **Minor-preserving subdivision, Lemma 20 (closed for h≥3).** The existing light-spanner
   subdivision proof needs an explicit clique-minor transport theorem.
   The new `SubdivisionMinor` module proves actual one-edge reflection for
   h ≥ 4. `MinorNormalization` now carries the invariant through actual
   repeated subdivisions, scaling and rounding, with explicit 2n−1 and 1/2
   quantitative bounds. `TriangleMinor` and `ThreeMinorNormalization` now
   close h=3 using actual cycle clique-models and the forest/tree argument;
   the combined theorem covers every h>=3.
3. **Actual clustering, Claims 22–23.** Must construct branch sets and
   short-cycle lifts with disjointness, connectedness and edge bounds proved.
   `ClusterGraph` now constructs the quotient minor and proves heavy-edge
   uniqueness intrinsically from weighted girth, including ties. It takes
   an explicit cluster family. The fourth batch constructs actual cycle
   lifts via edge removal and bounded host walks and proves Claim23 under
   those source invariants, with s≥4g. Hierarchy existence remains open.
4. **Charging, Lemma 24.** The proof is implicit in the cited BLWN17
   hierarchy. Its construction and charging invariants must be formalized;
   they are not accepted as a black-box hypothesis in a completed theorem.
5. **Girth-conjecture lower bound.** The explicitly conjectural premise is
   allowed by the paper. `girth_conjecture_sparse_lower_bound_all_h` now proves
   the full fixed-k sparsity family for h≥3 and every sufficiently large n,
   from that genuine premise alone. Exact finite edge extraction, rounded
   parameters, minor exclusion, copies/padding and the bounded-h star case
   are all constructed and proved. Constants and quantifier order are explicit.
   `girth_conjecture_connected_lower_bound` now strengthens this to an actual
   connected exact-n graph with a genuine unit-weight input MST and both
   lower bounds. The hub completion, bridge/girth argument, branch-set
   clique-minor localization, pendant reflection and MST existence/weight
   are proved. Its extra factor-two loss preserves the uniform h exponent.
   No disconnected MST ratio or minimum-spanning-forest convention is used.

## Completion gates

Local compilation, all-declaration allowed-axiom audit, independent kernel
replay, independent semantic review and exact-commit CI are recorded
separately. After the complete advertised scope is proved, a fresh skeptical
final auditor is required before a link is placed alongside this paper on
Greg's research website. Root coordinates that final audit and publication.


## Clique-threshold continuation

The eight-module follow-on constructs the deterministic minor-minimal
neighborhood step from Alon–Krivelevich–Sudakov (arXiv:2202.08530, page 2):
an integer-density-d graph has a genuine nonempty minor neighborhood with
at most 2d vertices and minimum degree at least d. Exact simple-graph
contraction counting and the positive-order minimum are proved internally.
This is not the full Kostochka–Thomason bound. The next fourteen modules now construct an explicit O(h log h) threshold
through actual separators, short walks, greedy dominating sets and disjoint
connected branch-set iteration. This preserves the paper's unspecified
polylog(h) factor at this dependency, but does not prove the sharper cited
threshold or the separate small-dense-subgraph density increment. Its
local aggregate, kernel replay, component review and exact-commit CI gates
are listed separately in the status file.

## Full-star selection continuation

The next seven-module candidate constructs the actual finite induced-star
family of Postle Lemma 4.1 (page 9): finite maximum, literal alternating
reassignment and one-leaf gain, simple directed chains, reachable saturated
centers, and an injective boundary-conflict count. The endpoint provides
actual disjoint induced-star branches, exact selected vertex cardinality and
a bounded simple quotient minor. The ordinary claw application uses ell>=1
and a nonempty A to obtain a nonempty family. No supplied packing or
augmentation oracle is accepted.

The seven-module quotient deletes unselected host vertices. Its local gates
and independent review pass; exact71 CI is running. The four-module follow-on
constructs actual mate-free stars and the full covering contraction retaining
all residual singleton branches. It proves exact vertex loss and width, with
the small-left upper-degree premise explicit. Its75-module local gates and independent exact-source review pass;
exact CI remains a separate gate. Cleaning/edge-loss
budgets and the density-increment trichotomy remain open.


## Actual accounting continuation (84-module candidate)

Nine new modules construct the exact-left-regular graph while preserving its
actual minor relation; count real simple-quotient fibers and internal edges;
remove degree-large star centers from a supplied complete cover; characterize
actual opposite crossings; choose a finite minimum of the ordered bad-pair
count at fixed centers and covered leaves; and double-count actual ordered
common-neighbor incidences. All production builds, root/index/axiom gates and
nine official kernel replays pass. Fresh exact-source semantic review passed.
Exact84 CI is tracked
separately. No global fiber-allocation bound, quantitative bad-pair estimate,
cleaning lemma, density increment or main upper theorem is obtained here.
The concrete two-star swap helper is outside this production freeze.


## Actual forest/swap continuation (88-module candidate)

Four exact-source reviewed modules supply a literal two-star leaf exchange,
an actual acyclic forest-valued subgraph with exact edge count, an internal
left-degree regularization preserving those forest edges, and a true union
of stars meeting two host neighborhoods. All strict builds/root/index,
816-declaration axiom audit and four official kernel replays pass. The swap's
original-host union mate-freeness premise remains explicit. The neighborhood
union includes every meeting star; it does not claim to be exactly the
source's domain excluding its distinguished component. No quantitative
bad-pair bound, cleaning lemma or main upper theorem follows yet.


### Finite swap-accounting boundary (new six-module draft)

`DirectedCrossingBudget` bounds actual selected-selected fiber suppression
by directed collisions and the ordered bad-pair score; residual-branch
fiber allocation is not yet proved. `MatedStarCount` and
`UnmatedBadIncidence` count actual common-neighbor mate incidences and
partition actual unmated bad neighbors by unique crossing leaves.
`BadForestWitnesses` gives the exact ordered score as a finite set of
forest-edge pairs, with actual host-edge semantics under `IsStarPacking`.
`BadWitnessSwapLoss` internally chooses a true finite minimum and proves
that admissible exchanges create at least twice the corresponding actual
unmated incidence class in new ordered witnesses. It does not assume a
minimum-score oracle in its existence endpoints. `SwapBadPairCharge`
provides the actual exceptional common-neighbor classification and an
original-host mate-free count; its quotient endpoint uses an actual simple
fiber of two host edges. No total new-witness upper bound or quantitative
cleaning theorem follows until the remaining graph classification and
induced-neighborhood charge are proved.


### Actual dense-witness boundary (100-module candidate)

`NewBadWitnessClassification`, `SwapNeighborUnion`,
`InsertedWitnessDegree`, `NewWitnessBudget`, `StarPartnerDegreeSum` and
`UnmatedDenseWitness` close the total new-witness classification and actual
induced-neighbor charge left open at94. The literal induced graph includes
the distinguished old star, so its vertex budget is proved directly.
Actual partner vertices, disjointness and handshaking give the quadratic
edge budget. The internally selected minimum is part of the conclusion,
not an oracle hypothesis. The stronger square bound needs M>=4*ell*q.

The next local-incidence consequence must either retain the small dense
induced graph as an explicit alternative or assume its absence explicitly;
Unmated alone is not such an absence hypothesis. The quantitative cleaning,
all-fiber contraction loss, density increment and spanner upper joins remain
open. No new source defect follows from this component theorem.


### Quantitative incidence and all branch categories (107-module candidate)

Seven new sources convert the actual quadratic witness into a real induced
small-dense alternative or a quantitative per-leaf incidence bound, retaining
4ellq<=r and smallness of every covered branch vertex. They assemble literal
mate counts and unique-leaf classes into the ordered bad-pair budget.
Actual covering quotient fibers, including singleton residual vertices,
are identified and their collision/zero-loss bounds proved. A conservative
ordered sum pays every branch category with4*collisions+bad-pair score.
The exact host-edge budget wrapper remains outside the production freeze;
the density increment and main spanner upper results remain open.

### Actual clean covering-minor alternative (109-module candidate)

Two sources close the exact host-edge budget left outside107. The real
simple quotient retains every residual vertex, and every internal/crossing
fiber is paid in the edge-loss identity. The resulting alternative provides
an actual small dense induced H or an internally chosen full mate-free
family M and a genuine covering bounded minor Q with exact vertex loss
and a quantitative edge-loss coefficient. The initial full mate-free family,
all selected-vertex degree bounds, literal Unmated and4ellq<=r remain explicit.
There is no supplied cleaning conclusion or minimum/bad-pair oracle.
The regularization/selection application and density-increment/main-upper
assembly remain open. The separate outside-frozen inverse-cubic numerical
route is not part of this candidate or its two-source component review.

### Scaled cleaning and selected induced host (114-module candidate)

Five sources provide an actual scaled cleaning alternative, literal covered
vertex/center/leaf subtype maps, exact induced boundary-degree loss and
forest-preserving integer-degree regularization. All common-neighbor and
mate-free transfers use proved injections/monotonicity. No global Unmated
heredity is asserted. The original family and all scalar-domain premises
remain explicit at the cleaning endpoint. Actual application of the new
regularized host to the later density-gain/iteration theorem remains open.
The separate global and bipartite Postle parameter conventions must not be
conflated; the conservative inverse-cubic route proves one domain only.


## Actual single-clean-star continuation

The139-module candidate proves `exists_clean_star_or_dense` for an actual
finite simple host, center c and actual neighbor set T. For natural k>=1,
real K,d>=1,0<=eps1<=1,eps2>=0,eps2*d>=1,k<=eps1*d,
2eps1*d<=|T| and original degrees <=K*d on {c} union T, it constructs
an actual induced S with |S|<=3*k*(K*k)*d and at least eps1*eps2*d^2/2
edges, or a full covering k-bounded minor with one k-vertex star branch,
all other branches singleton and total edge loss <=2(k-1)*eps2*d.
Each real edge contraction preserves the literal quotient and branch sizes;
its exact loop/parallel suppression is counted. The generic growth endpoint
also accepts an actual initial state, with its invariants explicit. It does
not yet encode the protected-old-branch forest invariant needed for maximal
clean-forest additions and replacements. Those constructions and the global
density iteration remain open. No additional source correction is asserted.
