# Higher-dimensional conditional theorem and remaining lattice estimate

The unconditional d=2 theorem is complete in its recorded scope. For general
dimension, the remaining mathematical input is now one explicit sharp vertex
count. The integer parameter selection and analytic conversion have complete
Lean proofs; the new graph wrappers are undergoing exact-commit CI.

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
had passed build and declaration audit when this next extension was prepared.

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

The exact `HigherParameters` and `HigherRate` source modules compiled locally
with `autoImplicit=false` and passed local kernel replay. A separate 12,000-case
integer sanity test covered all four regimes in dimensions 1 through 6; it is
not an independent proof. The two graph-assembly wrappers still require the
whole-checkpoint build, all-declaration axiom audit, and sequential project
kernel replay in exact-commit CI. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Local checks are not a claim that this full gate has
already passed, and imported mathlib is not freshly kernel-replayed in full.

Full Theorem 4 remains incomplete until the sharp lattice vertex count is
proved. The paper's separately documented printed superquadratic implication
is not repaired by this conditional theorem.
