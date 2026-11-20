# Constructing a rational edge family at the original factor

This record describes checkpoint `3c37a869966f73f812459ab411f2d9983666de77`. The later instance-factor search and actual-arc fallback have a separate verification record. [Derived factor and arc-count horizon](RATIONAL_DERIVED_EDGE_FACTOR_20261120.md)

`RationalOriginalEdgeFamily.adaptive` takes the original rational graph weights and a supplied rational factor. It computes the original threshold demands once. Its exact rational minimum-cost search excludes the chosen light arcs from candidate cuts and checks every candidate in the original graph. Excluded arcs remain available to traversing paths.

The construction first tests whether the factor times the total weight of arcs below the cutoff is at most one quarter. When the test succeeds at the vertex-count cutoff it uses a horizon linear in that count up to logarithmic factors. Otherwise it uses a horizon based on the squared vertex count. At factor zero it returns a single empty cut. The kernel checks validity and the original-weight marginal bound with multiplier eight.

`law_at_original_factor` identifies the uniform law over the returned list indices at the exact least integer factor for the original total weight. The executable routines take the factor as an input. `draw` uses the existing verified bounded-rejection sampler on literal bits. Lean checks the consumed prefix, the unread suffix, the validity of each returned cut, and the distribution of failures and successful inclusions.

The native fixtures returned 21 cuts with the vertex-count horizon and 57 with the general fallback. The excluded first arc in a two-arc path forced the second arc into the cut. Another case drew the expected cut using five bits and preserved the three-bit suffix. Zero trials consumed no bits. The exhaustive selector is exponential. An efficient exact-factor oracle and the general near-linear uniform family remain open.
