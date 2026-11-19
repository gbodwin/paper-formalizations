# Weak-cut marginals at the original factor

`WeakDecomposition.law_of_all_cost_factor` takes the all-cost rounding
property at a factor α and gives a finite distribution on admissible cuts.
Every supported cut is valid, and the probability of selecting item `e` is
at most `α * w e`.

The proof separates the convex hull of the admissible cut indicators from
the coordinatewise upper bounds if they are disjoint. The nonnegative part
of the separating prices is a valid oracle input. The oracle’s cut
contradicts strict separation. A finite convex combination supplies the
probability mass function, including multiplicities under its map to cuts.

`vertex_law_of_exact_factor` and `edge_law_of_exact_factor` apply the result
at the unchanged original weights, including zero weights and zero factors.
On `Fin n`, `ExactFlowCutGap.vfg` and `ExactFlowCutGap.efg` are the least
natural factors valid for all graphs and weight vectors of total `W`.
The headline bound supplies an admissible integer for edges, and the
elementary threshold cut supplies one for vertices. The corresponding
`vertex_law` and `edge_law` use these least factors at the input's own total.

The finite law can have arbitrary real probabilities. The separate uniform
construction has a quadratic cardinality factor at unrestricted original
edge weights. Its near-linear bound holds at the original factor under the
positive-weight floor, and the executable sampler uses the calibrated
headline bounds on general original input.
