# Rational edge solver and exact-weight weak decomposition

`EncodedEdgeSolver.bitTree` takes the original Boolean adjacency, rational
edge costs, and ordered demand list. It constructs the line graph, calls
the existing fractional covering solver, and runs dyadic rounding on the
original graph. It selects actual candidates by their exact rational edge
cost. The line graph has separate endpoint ports, so an input edge is
charged even when it touches a demand endpoint. A self demand yields the
length-zero obstruction.

The path projection and lifting prove equality of the original edge
distance and the represented vertex distance. The cost identity ties the
incumbent and final output to original edge prices. Both modes meet their
ideal expected bounds against every feasible fractional comparator. Every
supported output is an original-edge cut or certifies infeasibility of the
instance. For any positive bound `B` on the ideal expected price, the
bounded fair-bit solver exceeds `2 * B` with probability at most
`(max 1 n)^(-κ)`.

`WeakDecomposition.edge_law_of_exact_weight_factor` uses the all-cost
rounding factor at the original weights. Marginal deletion probability
is at most `8 * α * w(e)`. The proof gives a finite family with a
quadratic cardinality factor in its horizon. The earlier linear edge
horizon uses the oracle at modified weights. A bound that combines
the exact-weight oracle with the linear edge horizon remains open.

The edge solver accepts typed input. A full theorem that charges every
deterministic bit operation from raw input through rounding is still
open for both modes.
