# New Results on Linear Size Distance Preservers

Source: Greg Bodwin, [arXiv:1605.01106v4](https://arxiv.org/abs/1605.01106v4),
30 December 2020. Library: `LinearDistancePreservers`.

**Current mathematical scope:** Theorems 1–3 have unconditional finite forms
with the model/domain qualifications below. The displayed Theorem4 rate now
has an explicit uniform proof for every fixed A>=0 and every N>=8,
2<=T<=N^(2/3), 2<=d<=A sqrt(log N), with coefficient-one loss
`exp(-(1004+7A)sqrt(log N))`. The original sharper near-threshold existential
assertion remains open. The fresh qualified whole-package audit applies to
939a39a9; the later construction-family obstruction and nine-module uniformity
proof have separate component reviews and gates. The entire original paper
is not complete. [Uniform theorem and proof](verification/uniform-growing-dimension.md).

Read the [statement-by-statement coverage inventory](verification/coverage-inventory.md)
for original domains, corrections, exact declaration names, and remaining
scope. The [verification record](verification.md) distinguishes local checks,
exact-commit CI, component reviews, and the
[qualified end-to-end audit](verification/independent-audit-939a39a9.md).
The audit found no mathematical blocker. Its one minor inner-depth wording
correction is applied in the inventory; its 91 mathematical modules are unchanged.

## Main upper bounds

`theorem_one` takes any finite directed adjacency relation, finite
nonnegative weights, and p indexed demand pairs. It constructs a subgraph
preserving all exact infimum walk distances with

```
|E(H)| ≤ 3n + 24p floor(cuberoot(n))².
```

Shortest-path attainment, deterministic consistent tiebreaking, routing,
branching, and batching are proved internally. Zero weights, loops, empty
graphs, repeated demands, and unreachable pairs are covered. Signed or
infinite edge weights are not in this theorem's domain.

`theorem_two` takes an arbitrary finite undirected simple graph and demand
set P. It constructs an actual subgraph preserving all native
`SimpleGraph.edist` values, including infinity, with

```
|E(H)| ≤ 2|P| + 12 matchingNumber V.
```

The extremal quantity `matchingNumber` is defined as the maximum edge count
of a graph partitionable into at most n induced matchings. Lazy shortest-path
trees, a favorable cut, ownership, and the induced-matching partition are
constructed. `matchingNumber_subquadratic` proves its epsilon/threshold
subquadratic bound by an actual application of mathlib's triangle-removal
theorem. The source's prose RS definition reverses the implication required
by its proof; this package uses the standard extremal interpretation.

## Weighted subset lower bound

`TheoremThree.bounded_range_lower_bound` proves, for every fixed natural C>0
and every `2≤T≤N` with `T³≤C³N²`, an actual graph on `Fin N`, exactly T
terminals, and finite positive symmetric weights such that every preserving
subgraph satisfies

```
T³ N² ≤ (32768 C)³ |E(H)|³.
```

The literal Euclidean weights displayed in Theorem 5 are incorrect for the
modular undirected graph. `WeightedConstruction.designated_not_shortest`
checks a simple competing path at n=30 per layer, ell=3, x=10 whose length
`4+2 sqrt(37)` is smaller than the designated `2 sqrt(82)`.

The same graph is repaired with slope weight `k*x²+1+a²`, for k+1 layers.
The package proves uniqueness against arbitrary native walks including
backtracking, exact counts and incidence, actual obstacle-product forcing,
integer separation of weighted costs, parameter selection, and exact-size
padding. At least two terminals are necessary. Distinct indexed paths are
asserted only at positive depth.

## Unweighted subset lower bound in every fixed dimension

`TheoremFourGeneral.displayed_lower_bound` has the quantifiers

```
∀ d≥2, ∃ K(d)>0, ∀ N T with 2≤T≤N, ∃ G on Fin N, ∃ S with |S|=T,
  every H≤G preserving all terminal edist values satisfies
  N^(2/(d+1)) T^((2d+1)(d−1)/(d(d+1)))
    exp(−4(d−1)/d sqrt(log N)) ≤ K(d) |E(H)|.
```

There is no direction family, flatness, volume, vertex count, capacity,
rounding, uniqueness, or edge-count premise. The d=2 case retains its explicit
constant 100663296 and independent primitive-direction proof.

The higher-dimensional chain is now fully joined:

1. `LatticeMinima` constructs actual successive minima and proves the product
   bound by Minkowski. `LatticeDual` constructs an integral cofactor dual
   using a genuine integral basis, yielding weak transference.
2. `LatticeFlatness` proves an explicit ellipsoid sandwich for spherical caps
   and constructs an actual nonzero integer normal of width `8d^(d+1)`.
3. `LatticeCapGrouping` covers the actual missed integer hull by shallow caps
   and finitely many normal/depth cells. It proves the rounded integer index
   and floor-divided lattice box constraints.
4. `LatticeSliceVolume`, `LatticeSlicing`, and `LatticeCellVolume` transport
   each actual cell through a volume-preserving axial coordinate map, apply
   Tonelli and a transverse annulus bound, and obtain the sharp normal/depth
   powers. Zero-normal cells are proved empty.
5. `LatticeShells` supplies the finite weighted double sum, and
   `LatticeMissedVolume.exists_missed_volume_bound` proves the actual eventual
   bound `Vol(B_R \ integerHull(B_R)) ≤ A(d)R^(d(d−1)/(d+1))` at
   natural radii, for d≥3.
6. `PolytopeApproximation` proves the sharp missed-volume lower bound for an
   arbitrary finite convex hull. `LatticeApproximation` identifies the actual
   integer hull and handles constants/thresholds. `LatticeVertices.uniform_vertices`
   gives one C(d)>0 with at least `b^(d(d−1))` actual vertices at radius
   `C(d)b^(d+1)`, uniformly for every positive integer b.
7. `LatticeHull`, `LatticeProduct`, `HigherParameters`, `HigherRate`, and
   `HigherBehrend` supply the native graph, Behrend outer ports, all integer
   ranges, exact-size padding, and literal real-power conversion.

**Remaining source-level scope:** The original Theorem 4 permits d to grow
with N up to O(sqrt(log N)). No quantitative bound on K(d) that establishes
that uniform range is claimed. Its “in particular” near-N^(2/3)
superquadratic assertion also is not established by the displayed rate:
`TheoremFourRateAudit.suppressed_expression_le` proves the obstruction for
a uniform square-root exponential loss. This bounds a lower-bound
expression, not graph edge counts, and does not refute the existential
assertion by itself.

## Valid fixed-gap superquadratic corollary

`TheoremFourGeneral.superquadratic_fixed_gap` in `FixedGap.lean` proves:

```
For every fixed epsilon>0 and every fixed real B, there is N0 such that
for every N>=N0 and every integer 2<=T<=N^(2/3-epsilon),
there is an actual graph on Fin N and exactly T terminals for which
all terminal-distance-preserving subgraphs satisfy E>B*T^2.
```

The dimension is chosen using only epsilon, then the already-proved fixed-d
constant is fixed, and finally the size threshold absorbs that constant and
B. A positive polynomial gain dominates the square-root exponential loss.
No dimension-uniform estimate is assumed. This supplies the genuine
fixed-exponent-gap superquadratic range. It does not establish the sharper
square-root-exponential near-threshold range printed in Theorem 4.

## Explicit coefficient and quantitative boundary

`LatticeHull.explicitRadius` now gives a closed ceiling formula for the
radius factor, and `uniform_vertices_explicit` proves its actual lattice
count. `TheoremFourGeneral.displayed_lower_bound_explicit` joins it to the
same exact-size graph theorem in dimension d=n+3, using the sharper real
coefficient

```
rateFactor(explicitRadius(n),n+3)^(1/((n+3)(n+4))).
```

This removes the arbitrary existential choices in the fixed-d constant.
`UnitVolumeBounds` proves `(2/d)^d <= Vol(B_1^d) <= 2^d` and the adjacent-
dimension volume ratio bound by coordinate-cube inclusions. The quantitative bounds and their actual graph consequences are stated next.

## Quantitative growing-dimension theorem

The new `CoefficientBounds` and `RateFactorBounds` modules prove the explicit
bounds C(d)<=d^(20d²), rateFactor(C(d),d)<=d^(100d⁵), and its positive
[d(d+1)]-th root <=d^(100d³), for every integer d>=3. All ceiling and
unit-ball-volume factors are included.

`TheoremFourGeneral.displayed_lower_bound_growing` then gives the actual
exact-N, exact-T graph conclusion with no multiplicative coefficient:

  N^(2/(d+1)) T^((2d+1)(d-1)/(d(d+1))) exp(-5 sqrt(log N)) <= E,

provided 2<=T<=N and 100 d³ log d<=sqrt(log N). Here d may vary with N;
there is no hidden dimension-dependent constant or eventual threshold.
The condition is deliberately conservative. Its order is roughly
(log N)^(1/6)/(log log N)^(1/3), much smaller than the printed
O(sqrt(log N)) dimension range.

The exact full-paper boundary remains unchanged: the printed growing-d
range and sharper near-threshold existential assertion are not proved.
The expression obstruction is not a graph counterexample.

`TheoremFourGeneral.superquadratic_growing` adds the terminal cap
`T<=N^(2/3-1/d)` to the same dimension budget and proves
`T² exp(sqrt(log N)) <= E` for every preserving subgraph of its actual
exact-size graph. The parameters N,T,d may vary together.

`TheoremFourGeneral.displayed_lower_bound_quantitative` also removes the
budget restriction entirely, keeping the explicit loss
`exp(-4 sqrt(log N)-100 d³ log d)`. Its terminal-normalized form
`terminal_lower_bound_quantitative` gives, for any real epsilon and
`T<=N^(2/3-epsilon)`,

```
T² exp(eta log N-4 sqrt(log N)-100 d³ log d) <= E,
eta=(3d epsilon+epsilon-2/3)/(d(d+1)).
```

All statements require d>=3 and 2<=T<=N. These are finite theorems;
no asymptotic optimization of dimension is claimed.

## Verified weaker near-threshold range

`TheoremFourGeneral.superquadratic_sixth_root` proves a clean finite
consequence with no user-supplied dimension: if `log N>=16^6`, `2<=T<=N`,
and

```
T <= N^(2/3) exp(-8 (log N)^(5/6)),
```

then an actual N-vertex graph with exactly T terminals forces
`T² exp(sqrt(log N)) <= E` for every terminal-distance preserver.
The proof chooses the actual integer `d=floor((log N)^(1/6)/4)` and checks
all rounding, coefficient, and radius-domain requirements.

`superquadratic_sixth_root_eventual` expresses the corresponding precise
superquadratic quantifiers: for every real factor B, there exists N0 such
that every N>=N0 and every admissible T in this range admits a graph whose
every preserver has `E>B*T²`. The factor is chosen before the eventual size
threshold, and T may vary with N. The numerical threshold above is coarse.

The intermediate `superquadratic_optimized_budget` gives a stronger
parameterized sufficient condition: d>=3, `T<=N^(2/3-1/d)`,
`200d⁵ log d<=log N`, and `12d²<=sqrt(log N)` imply the same explicit
`T² exp(sqrt(log N))` lower bound. No asymptotically optimized choice of d
for this stronger budget is claimed.

The exponent-5/6 deficit is larger than the source's printed square-root
logarithmic deficit. The latter existential assertion remains unresolved and is not refuted by
these results or by the separate displayed-expression obstruction. The new
uniform theorem now covers the displayed dimension range.

## Verification

Run from the repository root with the pinned Lean/mathlib:

```sh
lake build
bash scripts/CheckModuleIndex.sh
lake env lean -DautoImplicit=false scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The defining-module audit includes all private/generated declarations and
permits only `propext`, `Classical.choice`, and `Quot.sound`. Every source
module is kernel-replayed; the aggregate import index is checked for omissions.
New-module local verification and exact-commit CI are recorded separately.
The [source hash manifest](verification/final-geometry-source-hashes.json)
binds the full paper-module set and original PDF/TeX.

Earlier proof maps, detailed construction discussions, and incremental
checkpoints remain in the [historical development record](verification/history-through-flatness.md).
Their old “remaining gap” statements are historical, not current status.

## Construction-family limit

A new finite theorem bounds the entire current sharp-direction product
family by E<=2 T² exp(27K²/8) at a fixed K square-root logarithmic terminal
deficit, even with ideal outer capacity. This is a method-specific obstruction,
not a disproof of the original existential claim.
[Exact scope](verification/construction-family-obstruction.md).
