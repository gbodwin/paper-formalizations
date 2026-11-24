# Exact normalized vertex optimization and amplified sparsest edge cuts

## Vertex lengths and the original vertex cut

`NormalizedVertexLP.minimize` constructs rational inequalities with one
length per vertex and one potential per demand and vertex. A separate last
coordinate bounds the objective. The arc inequalities charge a departure
from the current demand's source zero. In a simple path its target never
departs. The resulting path length counts exactly the internal vertices.

When all demands are reachable, `minimize_attained` verifies that the
computed rational assignment reaches the requested total demand distance
and attains the least price among all feasible real nonnegative lengths.
With at least one pair whose endpoints differ and have no direct arc,
total distance at least the number of demands is feasible.
This also gives a positive computed harmonic threshold.

`NormalizedVertexLPRound.run` solves this LP, chooses the smaller scale
by an exact comparison of sixth powers, and rounds on a literal tape.
The completion theorem returns an original vertex cut separating at
least one demand and the exact unread suffix, under reachability, the
nonadjacent-pair condition and the stated tape budget. Distinct demands
and a positive sparsity bound give the finite-tape failure bound
`1/2 + drawBound n * 2^(-T)` at twice the smaller scale with a common
constant. When the optimum is zero, every returned cut has zero cost.
The optimizer uses exhaustive Fourier–Motzkin elimination.

## Edge cuts with a tunable failure bound

`AmplifiedBudgetedSparsestEdge.run` computes the rational budget
candidates once. With the chosen assignment, it repeats the selected
rounding at its harmonic threshold and retains the sampled cut of
smallest actual sparsity. The score removes precisely the selected
arcs and tests each original demand's connectivity using the verified
binary path engine. It divides original arc cost by the number of
separated pairs. Every produced cut uses original arcs and separates
at least one demand in the distinct-pair domain.

For distinct reachable demands with at least one non-self pair, the
failure event is an original cut exceeding twice the cost-and-mass
comparator bound in either mode. Its probability is at most
`2^(-(extra + 1)) + 2^(-confidence)` on the stated uniform tape.
The complete run reads at most the explicit polynomial tape bound in
the vertex count and numerical confidence parameters, and returns
the exact unread suffix. The free-arc branch returns a zero-cost
original cut whenever it returns. The proof accounts for fair-bit
rejection even when draw ranges depend on the preceding bits.

The fixtures check the exact vertex price 3/2, endpoint exclusion,
a zero-cost vertex cut, and infeasibility for direct and self demands.
The edge receipts cover the optimized positive and free entries.
A separate scored draw fixture verifies genuine bit consumption,
a rejection, the minimum among sampled masks and the unread suffix.

This checkpoint leaves a complete structural bit-time bound and
high-confidence vertex amplification open.
