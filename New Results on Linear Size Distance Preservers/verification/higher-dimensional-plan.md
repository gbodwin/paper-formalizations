# Remaining higher-dimensional Theorem 4 work

This is a mathematical roadmap, not an additional Lean theorem or an assumed
axiom. The d=2 result is separate. The graph construction and metric forcing
are already available in arbitrary finite coordinate dimension.

## Sharp geometry

The source paper cites Bárány and Larman, *The convex hull of the integer
points in a large ball*, Math. Ann. 312 (1998), 167–181.
[Author-hosted primary source](https://www.renyi.hu/~barany/cikkek/73.pdf).
Its sharp vertex lower bound is based on a missed-volume estimate and a
polytope-approximation bound. The missed-volume argument invokes lattice
flatness. The relevant theorem was not found in the pinned mathlib search;
ordinary Minkowski/Blichfeldt machinery is available, but is not by itself the
required estimate. Only the vertex lower bound is needed here, not every
face-count estimate in that paper.

A sufficient interface for each fixed d≥2 would give, for every positive b,
an injective average-rigid family of b^(d(d−1)) nonnegative integer vectors
in d coordinates, each coordinate below c_d b^(d+1), for one fixed positive
integer c_d. Constants and any initial threshold can be enlarged. Translation
preserves the average-rigidity condition used by the graph construction, so
the stronger coefficient-sum-at-most-one convention is unnecessary.

## Parameter-selection template

Conditional on that geometric interface, the following arithmetic generalizes
the proved d=2 choice. Let

```
D = d(d+1), A = c_d^d
u = floor_root_D(N / ((A+2)M))
v = floor_root_(d²)(Q / A).
```

In the middle range u≤v≤u², set

```
b = floor(v/u), t = floor(u/b)
x = b^(d(d−1))
k+1 = t^d
n = c_d t^d b^(d+1).
```

The inequalities ub≤v≤2ub and tb≤u≤2tb imply

```
n^d x = A (t b²)^(d²) ≤ A v^(d²) ≤ Q
2M + M(k+1)n^d ≤ (A+2)M u^D ≤ N
M u^(2d) v^(d(d−1)) ≤ 2^(2d²) E.
```

The final inequality uses E=M n^d x(k+2). The upper root-rounding bounds
then produce a dimension-dependent constant C_d with

```
M^(d(d−1)) Q^(d²−1) N^(2d) ≤ C_d^D E^D.
```

For u=0 use a padded clique. For v<u use an endpoint-forced path. For
v≥u² use a padded clique and Q≤M. These are the same exhaustive regimes
used by the checked planar arithmetic. Their general-dimensional versions
still need Lean proofs; the displayed identities are not kernel claims.

Finally choose R=floor(T/6), M=3R, Q=rothNumberNat R when T≥6. The checked
planar terminal-scale lemma itself is independent of d and provides
2M≤T≤4M and T exp(−4 sqrt(log T))≤12Q. Taking D-th roots would yield

```
E ≥ c'_d N^(2/(d+1)) T^((2d+1)(d−1)/(d(d+1)))
    exp(−4(d−1)/d sqrt(log T)).
```

The small terminal cases use the path baseline. Thus this roadmap separates
the difficult geometric existence theorem from the general-d integer
arithmetic and final algebra. It does not claim to repair the paper's
separately documented superquadratic implication.
