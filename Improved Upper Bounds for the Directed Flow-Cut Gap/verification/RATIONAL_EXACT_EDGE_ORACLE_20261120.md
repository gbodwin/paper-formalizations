# Exhaustive original-factor edge oracle

`RationalExactEdgeOracle.select` enumerates subsets of the actual arcs. It checks each candidate using the binary shortest-path routine on the candidate's indicator weights in the original graph and minimizes the rational cost among valid cuts. When the finite demand list is infeasible it returns no cut.

`RationalExactEdgeOracle.original_factor` proves that on the original weight threshold demands the selected cut is valid and its rational cost satisfies the least integer factor `efg(n,W)` at the original total. The routine takes rational prices and needs no numerical value of that factor. The search is exponential in the number of arcs. An efficient exact-factor implementation and the general near-linear uniform family at the original factor remain open.

The two-arc fixture has an original threshold demand at distance one. Reversing the price order reversed the cheapest cut. The infeasible self-demand returned no candidate.
