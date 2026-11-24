# Exact normalized edge optimization and literal-tape rounding

The executable input consists of a directed adjacency matrix, rational
nonnegative edge prices and a vector of demands. The optimizer generates
linear constraints on edge lengths and one vertex-potential row per demand.
When all demands are reachable, the constraints express that the sum of
their shortest-path distances is at least the demand count. The potential
rows avoid enumerating paths when constructing the constraints.

`NormalizedEdgeLP.findWeights` checks a rational price budget and recovers
rational lengths when feasible. `NormalizedEdgeLP.minimize` uses
Fourier–Motzkin elimination to compute the smallest feasible objective and
recover lengths that attain it. `minimize_attained` compares the recovered
optimum against every feasible real nonnegative length assignment, including
zero prices. The elimination can grow exponentially.

For a nonempty, reachable demand vector admitting positive normalization,
`NormalizedEdgeLPRound.optimal_complete` proves that either rounding mode
returns an original cut and the exact unread suffix on any tape with the
stated bit budget. `optimal_cut_valid` proves the cut uses only original
arcs and separates at least one original demand. The optimizer and threshold
are computed from the input.

For distinct demands and a positive optimal price, the finite uniform-tape
theorems bound the probability of sparsity above twice the proved ideal
bound by one half plus `drawBound n · 2^(-T)`. The size mode uses the
harmonic factor times the size-rounding factor. The mass mode uses the
harmonic factor to the power three halves times the square root of the
average-normalized mass of the lengths returned by the optimizer. Both
scales multiply the optimal price divided by the demand count.

The executable fixture tests the exact fractional cost 3/2, rejects a
smaller budget, and checks that both modes return the original arc cut and
preserve the unread tape. It also checks a zero-cost optimum and
infeasibility of positive normalization for a sole self demand.

Polynomial optimization, the executable vertex threshold, and a
finite-tape approximation bound at zero optimum remain open.
