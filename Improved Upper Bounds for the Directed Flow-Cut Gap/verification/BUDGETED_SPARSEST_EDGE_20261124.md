# Joint price and mass control for the bounded sparsest-edge solver

The optimizer generates rational doubling grids for price and mass.
The endpoints depend only on the original graph, prices and demand count.
For each positive budget pair the executable covering iteration uses
the arc price divided by the price budget plus the reciprocal mass
budget. It returns lengths with total demanded distance at least the
demand count.

When every demand is reachable in the positive-price subgraph,
`ConcurrentEdgeBudgetGrid.nearby_candidate` proves that one generated
assignment has original fractional cost and total mass each within
twelve of any real normalized comparator. The proof caps comparator
lengths at the demand count and witnesses budget pairs within a
factor of two. The algorithm computes all of these candidates from
the rational input.

`ConcurrentEdgeBudgetSelection.choose` chooses a candidate and size
or mass mode by comparing exact rational sixth powers of their
sparsity scales. The selected original-cost scale is at most 48
times either comparator scale. At average demand distance one,
the comparator scales use fractional cost per demand and the
comparator's total normalized mass. One uniform constant works for
both modes.

`ConcurrentEdgeBudgetRound.run` computes and rounds the selected
assignment on the original tape. Completion assumes all original
demands are reachable, at least one has different endpoints, and
the stated tape budget is available. A returned cut uses original
arcs and separates at least one demand. The finite-tape bound uses
distinct demands and the computed positive threshold, and gives
failure probability at most one half plus `drawBound n · 2^(-T)`
at twice the comparator bound. If removing free arcs disconnects
a demand, the free-arc branch gives zero cost on every returned cut.

The native fixture selects the mass mode on one arc and the size
mode on a graph with opposite demands. It also runs the free-arc
branch and checks the actual original cut and unread tape.

This implementation uses bounded covering updates and rational
budget enumeration. Complete deterministic bit cost, high-confidence
amplification, and the vertex fractional optimizer remain open.
