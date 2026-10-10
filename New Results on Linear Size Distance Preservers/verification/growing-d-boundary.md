# Fixed-d proof, uniform constants, and the printed final implication

Status: 10 October 2026, following commit 608fc6b0. This is an audit/research
note, not a claim that the quantitative estimates below have Lean proofs.

## Certified statement and pending exact-commit checks

TheoremFourGeneral.displayed_lower_bound, at 306cd425, states:
for every integer d>=2 there exists a positive integer K(d), selected before
N,T, such that every 2<=T<=N admits an actual graph on Fin N and exactly T
terminals, forcing

  N^(2/(d+1)) T^((2d+1)(d-1)/(d(d+1)))
    exp(-4(d-1)/d sqrt(log N)) <= K(d) E.

No geometric premise remains. Full exact-commit CI 38070056988 passed at 17:23:22 UTC; the seven-module
local gate and independent bounded semantic review also passed. Commit 608fc6b0 adds the locally checked
and independently reviewed fixed-gap consequence: for every fixed eps>0
and real B, eventually all N and 2<=T<=N^(2/3-eps) admit an actual witness
forcing E>B*T^2. Its full exact-commit CI is also pending.

## A formally bounded expression, not a graph counterexample

The existing TheoremFourRateAudit.suppressed_expression_le proves, for
L=log N>0, log T=(2/3)L-t, d>=1, and 0<=t<=a sqrt(L), that the displayed
polynomial expression divided by T^2, with a loss exp(-c sqrt(L)), is at
most exp(27a^2/8-c sqrt(L)), uniformly in d. For fixed a and c>0 this tends
to zero. The algebraic upper bound is formally proved; a separate named
filter-limit theorem is not claimed. Taking a deficit (a+1)sqrt(L) also
makes T=o(N^(2/3)exp(-a sqrt(L))) while leaving this obstruction in place.

Therefore the displayed expression with a fixed positive uniform loss
cannot establish the printed near-threshold superquadratic implication.
This does not give an upper bound on optimal preserver sizes, does not
refute the existential graph statement, and does not resolve whether a
stronger construction might prove it. This obstruction is separate from
whether the hidden constants in the displayed rate are uniform in d.

## Exact current geometric coefficients

Write v_j=Vol(B_1 in R^j), d>=3, and set

  W = 8 d^(d+1), H = W^2+3W,
  D = 16 d(d-1) 3^(d-1) (W+1) H [2(W+2)]^((d-3)/2)
        (H+1)^((d-1)/2) v_(d-1),
  A = d v_d + D + 1,
  R0 = ceil(H+1)+1,
  J = 2^(d+2),
  C = ceil(max(4 J^2 A/v_d, R0))+2.

These formulas are obtained directly from cellCoefficient, deepCoefficient,
exists_missed_volume_bound, and uniform_vertices_of_missed_bound. Choosing
these ceiling witnesses gives the same sharp lattice conclusion. The new
ExplicitLatticeRadius module now proves this formula directly, with a passed
local compilation/replay/axiom gate and independent semantic review.

Elementary cube inclusions give (2/d)^d <= v_d <= 2^d and
v_(d-1)/v_d <= d^d/2. The following conservative estimates are elementary
mathematical calculations, not yet Lean-certified:

  W+1 <= d^(d+4), H <= d^(2d+7),
  2(W+2) <= d^(d+5), H+1 <= d^(2d+8),
  D/v_d <= d^(8d^2), A/v_d <= d^(8d^2+1),
  C <= d^(20d^2).

For the D estimate, replacing both fractional exponents by d/2 bounds the
sum of the powers of d by (3/2)d^2+(23/2)d+16 <= 8d^2 for d>=3.
The loose exponent 20 leaves room for both ceiling operations and sums.

## A concrete avoidable loss in the graph conversion

The published HigherRate.rate_of_power deliberately replaces an integer
power coefficient K by K itself. The exact coefficient is K^(1/D0), where
D0=d(d+1). RootRateDraft.lean records this sharper algebra and the actual
graph wrapper; it compiled successfully with autoImplicit=false at 17:22 UTC.
The assembled RootRate module and explicit-radius join passed the local
axiom/replay gate; their new exact-commit CI is separate.

With c=2C+1 and the literal HigherParameters.factor/HigherProduct.rateFactor,
the bound C<=d^(20d^2) gives conservatively

  rateFactor(C,d)^(1/(d(d+1))) <= d^(100d^3).

For example c<=d^(21d^2); the largest product term has d-exponent at most
21d^5+45d^4+d^2+2d before the smaller coefficient and sum factors. Taking
the d(d+1)-th root yields the displayed conservative estimate.

Thus the present explicit geometry, with that algebraic improvement, can
support an exp(-O(sqrt(log N))) loss when d^3 log d=O(sqrt(log N)), roughly

  d <= (log N)^(1/6)/(log log N)^(1/3).

This is weaker than the printed d=O(sqrt(log N)). It is a route to a new
uniform theorem, not an already completed formal result. Merely exposing
the existing constants does not establish the printed range.

Allowing the larger explicit constant loss and optimizing d around L/t
suggests a corrected superquadratic range with deficit

  t >> L^(4/5) (log L)^(1/5), L=log N,

because the polynomial gain is of order t^2/L while the coefficient cost
is of order (L/t)^3 log L. This remains an unformalized consequence of the
quantitative estimates, and is not advertised as a proved replacement.

## Possible improvement requiring additional proofs

The current shallow/deep split takes delta=R^(-(d-1)/(d+1)) without balancing
its dimension-dependent coefficients. Choosing a dimension-dependent
multiple of delta balances d v_d delta R^(d-1) against the deep coefficient
R^((d-1)/2) delta^(-(d-1)/2). The optimized coefficient is approximately the
2/(d+1)-th power of the current deep coefficient, reducing its logarithmic
dimension cost from O(d^2 log d) to O(d log d). After the graph root this
suggests O(d^2 log d) instead of O(d^3 log d), and a deficit of order
L^(3/4)(log L)^(1/4). Thresholds, ceilings, and all inequalities must be
proved before either improvement is claimed.

Even these prospective refinements do not recover the printed near-
sqrt(L)-deficit implication; the independent expression obstruction above
still applies. A proof of that existential assertion needs genuinely
stronger lower-bound information.
