# Bisection for the exact rational edge factor

Count the distinct tails and distinct heads of actual positive-weight arcs with different endpoints. Their smaller count is an upper bound on the number of positive-weight arcs on any simple path. The cutoff proof turns that count into an upper bound on the exact factor.

The support solver returns zero immediately when the cap is zero. Otherwise it tests whether the empty cut already meets every demand. If it does, the exact factor is zero. If it fails and the cap is one, the exact factor is one. These cases skip rational feasibility.

For the remaining inputs the solver prepares the valid cut constraints once. It searches the resulting positive interval by bisection, using the monotonicity of exact factor acceptance and preserving `leastSupported_eq`. The call counter is bounded by one plus the binary logarithm of the endpoint cap.

The improved bound applies to the number of exact feasibility calls. Enumerating candidate cuts and solving each rational feasibility system remain separate runtime obligations.

The native checks return factor two with two feasibility tests on the directed triangle. A four-vertex fan has cap one and returns factor one with no feasibility tests. The loop-only graph returns zero immediately. The subunit path has positive endpoint cap and returns zero because the empty cut suffices.
