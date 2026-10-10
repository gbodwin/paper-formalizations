# New Results on Linear Size Distance Preservers

Source: Greg Bodwin, [arXiv:1605.01106v4](https://arxiv.org/abs/1605.01106v4),
30 December 2020. Library: `LinearDistancePreservers`.

**Current mathematical scope:** Theorems 1–3 have unconditional finite forms
with the model/domain qualifications below. The displayed Theorem 4 rate is
now assembled for every fixed dimension d≥2 without a geometric premise.
The sharp actual lattice-ball vertex count is proved for d≥3. Uniform growing-d
constants and the printed final superquadratic implication remain outside
this result. This is not a declaration that the entire original paper has
passed its final independent audit.

Read the [statement-by-statement coverage inventory](verification/coverage-inventory.md)
for original domains, corrections, exact declaration names, and remaining
scope. The [verification record](verification.md) distinguishes local checks,
exact-commit CI, module reviews, and the still-required whole-paper audit.

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
