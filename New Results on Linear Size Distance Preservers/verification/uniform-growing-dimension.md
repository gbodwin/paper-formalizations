# Uniform growing-dimension lower bound

`TheoremFourGeneral.uniform_dimension_lower_bound` proves the following exact
finite statement, with every constant and parameter domain explicit. For every
real A>=0 and natural N,T,d satisfying

    N>=8, 2<=T, T<=N^(2/3), 2<=d<=A sqrt(log N),

there are an actual undirected unweighted simple graph G on Fin N and a
terminal set S of cardinality exactly T such that every H<=G preserving all
native terminal-to-terminal `SimpleGraph.edist` values satisfies

    N^[2/(d+1)] T^[(2d+1)(d-1)/(d(d+1))]
      exp(-(1004+7A) sqrt(log N)) <= |E(H)|.

A is fixed before all N,T,d, and the bound is uniform over that entire domain.
There is no direction, lattice-count, flatness, volume, scale-selection,
capacity or graph-forcing hypothesis supplied by the caller. The terminal
range contains the eventual range in the source's displayed Theorem 4.
The finite N>=8 condition simply makes the outer-vertex reservation automatic.

## Proof decomposition

- `BalancedVolume` scales the shallow/deep cutoff before summing the actual
  missing-volume cells. With Q=d^(40d) and R>=Q², the volume coefficient is
  `(dQ+1) Vol(B1)`.
- `BalancedRadius` derives actual lattice-ball vertex counts with an explicit
  radius constant at most d^(100d).
- `BalancedCoefficient` bounds the literal construction factor by d^(1000d^4)
  and its d(d+1)-th root by d^(1000d²).
- In the regime d³<=sqrt(log N), log d<=d absorbs this coefficient in
  exp(1000 sqrt(log N)), leaving total loss1004 sqrt(log N).
- `SphereScales`, `SpherePower`, `SphereCoefficients`, and `SphereTheorem`
  use the elementary equal-norm sphere directions instead of a sharp
  lattice-polytope count. They internally choose both real scales, floor them,
  treat path/clique extremes, reserve outer vertices, and substitute actual
  Behrend terminal scales, including the small-terminal cases.
- The sphere determinant is d²-2, and the graph coefficient is at most exp(7d).
  `SphereComparison` bounds the difference from the desired sharp polynomial
  by 4 log(N)/d³. Thus when sqrt(log N)<=d³ and d<=A sqrt(log N), the total
  loss is at most (8+7A)sqrt(log N).
- `UniformDimension` combines the two exhaustive regimes and the independently
  proved d=2 construction, using the common loss(1004+7A)sqrt(log N).

## Verification and limits

All nine new source modules are assembled from individually compiled and
independently reviewed components. The assembly manifest records each exact
input source hash and output hash. Assembly changes imports and removes four
progress-print commands; it does not replace any proof argument or premise.
The final production-source gates and their exact-hash review are recorded
in the adjacent verification record. Full CI for the new checkpoint is a
separate gate. The fresh end-to-end audit at939a39a9 still applies only to
its unchanged91 mathematical modules; component review is not relabeled
as an extension of that audit.

This closes the original displayed growing-dimension rate. It does **not**
establish the printed near-threshold superquadratic existential assertion.
The existing certified replacement has a(log N)^(5/6) deficit. The formal
count-family upper envelope shows why improving constants or outer capacity
within that sharp-direction product family alone cannot repair a fixed
square-root-logarithmic deficit. It does not disprove arbitrary graph existence.
Other source corrections and auxiliary scope restrictions remain in the
statement-by-statement inventory; the entire original paper is not complete.
