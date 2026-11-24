# Bounded iteration for a normalized edge cover

The normalized sparsest-edge covering problem uses a joint path profile.
A column contains one path for each demand. A shared arc contributes its
multiplicity across those paths. The executable oracle calls the binary
shortest-path routine for each demand and uses the resulting minimum-length
profile. It selects the positive coefficient with smallest price divided
by coefficient to determine the update amount.

`MultiplicityCover.solve_stopped` proves that the rational covering
iteration reaches its stopping condition within the declared
`3 * (n * n)^2` update budget. For strictly positive arc prices and
reachable demands with at least one pair of different endpoints,
`ConcurrentEdgeCover.solve_normalized` and `solve_price_le` give a cover
with total demanded distance at least the demand count. Its cost is at
most three times that of every feasible real comparator.

`ConcurrentEdgeCappedPrices.solve_spec` covers all nonnegative rational
prices with factor six. It first checks whether a demand is disconnected
after removing free arcs. In that case assigning length to free arcs
gives normalized distance at zero cost. In the remaining case a positive
rational price floor bounds the cost of any normalized comparator.
Clipping comparator lengths at the demand count preserves normalization.
The solver adds a small charge to free arcs and uses the positive-price
iteration. Lean checks the resulting cost against the original prices.

`ConcurrentEdgeRound.complete` runs the original literal-tape edge
rounder from the computed lengths, with an exact unread suffix and
sufficient tape. Its cut contains only original arcs and separates at
least one demand. `size_probability` compares finite-tape sparsity
against any positive-cost normalized comparator for distinct reachable
demands, with the factor six absorbed into the size guarantee.
`zero_cut_price` gives zero cost on every returned cut when a normalized
zero-cost comparator exists.

The fixture checks multiplicity two on a shared arc and the corresponding
bottleneck choice. It measures a normalized demanded distance sum of
two with recorded original cost 823250362/774422237 against optimum one.
It exercises a cut using the original shared arc, a normalized free
cover and cut, and the positive-path branch with mixed prices.

The proofs bound the update count and the output guarantee. Complete
deterministic bit cost, a bound preserving the comparator's normalized
mass, and the executable vertex sparsest-cut entry remain open.
