# Higher-dimensional conditional theorem and remaining lattice estimate

The unconditional d=2 theorem is complete in its recorded scope. For general
dimension, the remaining mathematical input is now one explicit sharp vertex
count. The integer parameter selection and analytic conversion have complete
Lean proofs; the new graph wrappers passed exact-commit CI38059438907.

## Concrete lattice-hull bridge

`LatticeHull.lean` defines the finite integer ball by its squared-coordinate
inequality and filters its integer hull's actual mathlib extreme points.
`image_vertices` identifies this filter with the complete extreme-point set.
`average_unique` proves that an average equalling a vertex is constant;
`exists_directions` selects any prescribed number of those vertices and translates
them into distinct nonnegative integer vectors, all coordinates below `2R+1`.

`LatticeProduct.lean` connects this family to native shortest distances,
Behrend outer ports, and exact-size padding. Its graph theorem assumes only
`x ≤ (vertices (ball d R)).card` and numerical product capacities. No direction
family, convexity, path-uniqueness, graph, or forced-edge oracle is assumed.
The core was locally compiled and kernel-replayed, and an independent source
review passed. The bridge checkpoint is `eb56bac15a54d8bf564672bdc148969a97a00292`;
[its exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38058322074)
passed the complete build, declaration audit, and sequential kernel replay.

## The single open geometric hypothesis

For each fixed d≥2, it is sufficient to prove that there is one natural C such
that, for every positive natural b,

```
b^(d(d−1)) ≤ (vertices (ball d (C b^(d+1)))).card.
```

This is a count of the concrete finite lattice-ball hull's vertices. It is an
explicit hypothesis of `HigherProduct.displayed_lower_bound`, not a new axiom,
not an imported unproved theorem, and not a claimed completed result.

The source paper cites Bárány and Larman, *The convex hull of the integer
points in a large ball*, Math. Ann. 312 (1998), 167–181.
[Author-hosted primary source](https://www.renyi.hu/~barany/cikkek/73.pdf).
Their vertex lower bound uses a missed-volume estimate, polytope approximation,
and lattice flatness. No ready sharp estimate was found in the pinned mathlib;
ordinary Minkowski/Blichfeldt machinery alone does not supply it. Only the
vertex lower bound is needed, not the paper's entire face-count theorem.
Constants and an initial radius threshold can be absorbed by enlarging C.

## Completed arithmetic and conditional assembly

`HigherParameters.parameters_or_baselines` handles every positive dimension
and all N≥2, M>0, 0≤Q≤M. Put c=2C+1, A=c^d and D=d(d+1), and choose

```
u = floor_root_D(N / ((A+2)M))
v = floor_root_(d²)(Q / A).
```

For u=0 use a padded clique. For v<u use an endpoint-forced path. For v≥u²
use a padded clique and Q≤M. In the remaining regime set

```
b = floor(v/u), t = floor(u/b)
x = b^(d(d−1)), k+1 = t^d, n = c t^d b^(d+1).
```

The proved rounded inequalities give

```
n^d x ≤ Q
2M + M(k+1)n^d ≤ N
M u^(2d) v^(d(d−1)) ≤ 2^(2d²) E,
```

where E=M n^d x(k+2). The source's explicit positive `factor c d` covers all
four regimes, proving

```
M^(d(d−1)) Q^(d²−1) N^(2d) ≤ factor(c,d) E^D.
```

`HigherProduct.capacity_lower_bound` assembles the actual graph from these
cases and the open vertex-count hypothesis. The choice c=2C+1 absorbs the
translation bound `2C b^(d+1)+1` without any extra asymptotic condition.

`HigherRate` proves the Behrend substitution, the small-terminal path bound,
and exact conversion to fractional real powers. `HigherBehrend` reuses the
proved terminal scales R=floor(T/6), M=3R, Q=rothNumberNat R for T≥6 and handles
T=2,...,5 with a path. Its conditional graph conclusion, for every 2≤T≤N, is

```
N^(2/(d+1)) T^((2d+1)(d−1)/(d(d+1)))
  exp(−4(d−1)/d sqrt(log N)) ≤ rateFactor(C,d) E.
```

`rateFactor` is a positive natural constant depending only on C and d. The
formula is the actual real-power theorem, not an informal interpretation of
an integer-power result. The only remaining caller-supplied construction input
is the displayed vertex-count hypothesis.

## Verification boundary

The general-dimensional conditional checkpoint `7fe209e4f49fdd81c079f2e3fba039a88ba1e72a`
passed [CI38059438907](https://github.com/gbodwin/paper-formalizations/actions/runs/38059438907)
at 14:39:14 UTC on 10 October 2026. The build, module indexes, complete axiom
audit (1,185 paper declarations), and all 95 project-module kernel replays
passed;61 replayed modules belong to this paper. Independent arithmetic and
analytic source reviews passed. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Imported mathlib is not freshly replayed in full.

## New proved geometric steps

`LatticeCaps` establishes actual attained support planes, lattice-free caps,
an explicit inscribed cylinder, the cross-section identity, and annulus
containment. `LatticeCapVolume` proves the full shallow-cap contribution:

```
Vol(union of all caps of height ≤ R^(-(d-1)/(d+1)))
  ≤ d Vol(unit ball) R^(d(d-1)/(d+1)),     R≥1.
```

The proof is for the actual Euclidean Lebesgue volume and works for an
arbitrary union of directions, so it needs no facet-count or disjointness
assumption. This completes the shallow-cap lemma, not the deep-cap cases.

`LatticeScaling` proves the exact conversion from any eventual estimate
`c R^(a/q) ≤ F(R)` with c>0 to `b^a ≤ F(C b^q)` for all b>0, for one
positive integer C. It handles real constants and initial thresholds
without assuming monotonicity of F.

These three modules passed full exact-commit CI 38061456670 at 6dcce790:
1,221 paper declarations audited,98 project modules kernel-replayed, 64 for
this paper. Independent read-only semantic review of both cap geometry modules passed.

## Further checked reductions

`LatticeBody` proves the exact Euclidean extreme-point correspondence and
identifies the missed region with the union of all lattice-free support caps.
`LatticeCapWidth` converts a supplied width certificate into the explicit
bound `h² normSq(q) ≤5W²`; it does not prove a flatness direction exists.

`LatticeShells` proves the single and double weighted lattice-normal sums,
including the natural floor in R/k and the reciprocal-square factor 2. For
d≥3, the coefficients are respectively 2d3^(d−1) and 4d3^(d−1), multiplying
R^((d−1)/2). The finite shell argument adapts the relevant portion of pinned
mathlib's ZLattice summability proof, with attribution retained.

The three modules passed local compilation, kernel replay, and a complete
45-declaration axiom audit; independent source review passed. Their whole-
checkpoint CI is submitted separately.

The outstanding sharp-count proof needs a lattice-flatness theorem for the
inscribed cap bodies, the actual deep-cap geometric grouping that feeds the
now-proved weighted sums, and a missed-volume upper bound. The approximation lower bound and its
conversion to the uniform integer vertex-count hypothesis are now proved
in `PolytopeApproximation` and `LatticeApproximation`. Facet-normal/covolume tools may be needed
for the source proof's grouping; none is silently assumed here.

Full Theorem 4 remains incomplete until the sharp lattice vertex count is
proved. The paper's separately documented printed superquadratic implication
is not repaired by this conditional theorem.


## Completed sharp approximation reduction

The new `PolytopeApproximation.missed_volume_lower_grid_scaled` is an
unconditional, actual-volume result: for d≥1, R>0, m≥1 and a finite V in B_R,
`2^(d+2) #V ≤ m^(d−1)` implies
`R^d Vol(B_1)/(4m²) ≤ Vol(B_R \ convexHull(V))`.

`LatticeApproximation.convexHull_vertices` makes this apply to precisely the
existing finite lattice vertices. `uniform_vertices_of_missed_bound` proves
that for each d≥2, an eventual `A R^(d(d−1)/(d+1))` missed-volume upper bound
implies the single uniform sharp vertex-count hypothesis of HigherProduct.
The constant C and every positive b are handled explicitly. Thus the remaining
flatness/grouping work can target the actual missed-volume upper bound alone.
