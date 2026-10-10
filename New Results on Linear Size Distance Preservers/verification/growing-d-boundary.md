# Quantitative dimensions and the printed final implication

Status: 10 October 2026. The first five growth modules passed the local
60-declaration audit, five kernel replays, indexes and exact-hash reviews.
The three clean-range follow-ons also passed their 17-declaration audit,
three kernel replays, indexes and exact-hash reviews. Full exact-commit CI
is recorded separately in `verification.md`. This note does not declare
the original paper complete or its final whole-paper audit passed.

## Previously certified conclusions

The unconditional fixed-d rate passed full CI at `306cd425`. The fixed-gap
corollary at `608fc6b0` passed full CI 38071062211: for each fixed epsilon>0
and target factor B, eventually every 2<=T<=N^(2/3-epsilon) admits an actual
exact-N, exact-T graph forcing E>B*T². Dimension depends on epsilon, and the
size threshold depends on epsilon and B.

The explicit-radius/root-coefficient checkpoint `d4938f26` passed full CI
38072235157: 3,660 build jobs, 1,518 paper declarations, all 117 project
kernel replays, including 83 paper modules. No geometric premise remains.

## Closed geometric and graph coefficient bounds

Write v_j=Vol(B_1 in R^j), d=n+3>=3, and set

  W = 8 d^(d+1), H = W²+3W,
  D = 16 d(d-1) 3^(d-1) (W+1) H [2(W+2)]^((d-3)/2)
        (H+1)^((d-1)/2) v_(d-1),
  A = d v_d + D + 1,
  R0 = ceil(H+1)+1, J = 2^(d+2),
  C = ceil(max(4 J² A/v_d, R0))+2.

These are the literal previously proved cap/volume/radius definitions.
`UnitVolumeBounds` gives (2/d)^d<=v_d<=2^d and
v_(d-1)/v_d<=d^d/2 from actual cube inclusions.

`CoefficientBounds` now proves, including both ceiling steps,

  D/v_d <= d^(12d²), A/v_d <= d^(12d²+1), C <= d^(20d²).

`RateFactorBounds` bounds the literal integer graph coefficient and its
positive root:

  rateFactor(C,d) <= d^(100d⁵),
  rateFactor(C,d)^(1/(d(d+1))) <= d^(100d³).

The constants are intentionally coarse, but they are proved for every
integer d>=3, rather than hidden in a dimension-dependent asymptotic term.

## Actual finite graph theorems

For every d>=3 and every 2<=T<=N,
`TheoremFourGeneral.displayed_lower_bound_quantitative` constructs an actual
graph on Fin N and a terminal set of cardinality T such that every preserving
subgraph satisfies

  N^(2/(d+1)) T^((2d+1)(d-1)/(d(d+1)))
    exp(-4 sqrt(log N)-100 d³ log d) <= E.

Under the numerical budget 100 d³ log d<=sqrt(log N),
`displayed_lower_bound_growing` gives the simpler uniform rate

  N^(2/(d+1)) T^((2d+1)(d-1)/(d(d+1))) exp(-5 sqrt(log N)) <= E.

The budget permits d to vary with N. Its order is roughly
(log N)^(1/6)/(log log N)^(1/3), which is smaller than the source's printed
O(sqrt(log N)) range. No hidden dimension-dependent threshold is used.

With the same budget and T<=N^(2/3-1/d), `superquadratic_growing` proves

  T² exp(sqrt(log N)) <= E.

All these inequalities apply to actual native-distance-preserving
subgraphs, with exact vertex and terminal counts. The d>=3 restriction is
explicit; the separately proved planar theorem remains available for d=2.

For any real epsilon with T<=N^(2/3-epsilon), the fully quantitative theorem
also gives `terminal_lower_bound_quantitative`:

  T² exp(eta log N-4 sqrt(log N)-100 d³ log d) <= E,
  eta=(3d epsilon+epsilon-2/3)/(d(d+1)).

No dimension budget is required for this last finite statement. Positive
growth follows whenever its displayed exponent is sufficiently large.
Choosing d near L/t, epsilon=t/L, suggests the sufficient asymptotic deficit
t >> L^(4/5)(log L)^(1/5), L=log N. This parameter-selection asymptotic is
not a separately formalized theorem and is not advertised as one.

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
logarithmic deficit. The latter existential assertion and the larger
printed uniform dimension range remain unresolved, and are not refuted by
these results or by the separate displayed-expression obstruction.

## Expression obstruction, not a graph counterexample

`TheoremFourRateAudit.suppressed_expression_le` proves, for L=log N>0,
log T=(2/3)L-t, d>=1, and 0<=t<=a sqrt(L), that the displayed polynomial
expression divided by T², with loss exp(-c sqrt(L)), is at most
exp(27a²/8-c sqrt(L)), uniformly in d. For fixed a and c>0 this tends to
zero. The algebraic bound is formal; a separate named filter-limit theorem
is not claimed. A deficit (a+1)sqrt(L) also makes
T=o(N^(2/3)exp(-a sqrt(L))) while leaving this obstruction in place.

Thus that expression with a fixed positive uniform square-root loss cannot
establish the printed near-threshold superquadratic implication. This is
not an upper bound on optimal preserver sizes and does not refute the
existential graph assertion. A stronger construction might establish it.

## Unresolved original scope

The printed O(sqrt(log N)) dimension range and its sharper near-threshold
existential assertion remain open. Balancing the shallow/deep geometric
constants may improve the current O(d³ log d) coefficient cost, but no such
refinement is included in these proofs. Even a coefficient improvement does
not by itself overcome the separate displayed-expression obstruction.
