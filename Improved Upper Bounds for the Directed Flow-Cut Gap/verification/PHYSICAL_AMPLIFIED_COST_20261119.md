# Polynomial bounds on the realized solvers’ recorded charges

`PhysicalVertexRoundingCost.polynomial_bound` joins the uniform chain, weighted port preparation and replication, and heavy-vertex removal with the packed integer round. The proof uses the actual size and projection bounds of each construction.

`PhysicalAmplifiedVertexCost.run_paid` accounts for each observed rounding call, both binary price comparisons, and amplification on the same tape. `PhysicalSolverCostEnvelope.vertex_polynomial` bounds the sum of dispatch, readback, rounding and selection counters in the original number of vertices and demands, stored price bits, and numerical confidence exponent. The proof bounds the shared rejection trial count constructed by the solver.

`PhysicalEdgeCostEnvelope.edge_polynomial` gives the corresponding bound on the edge runner’s counters. Its outer width bound uses the original edge price fields and its rounding dimension is the number of vertices in the dyadic gadget. `PhysicalEdgeFamilyCost.calibrated_polynomial` carries the same counters through each reached adaptive history, using the rational price width and total call count derived from the original stored weights and calibrated confidence.

The combined counters include reference-machine bit operations, binary price operations and the charged word operations of the vertex reductions. The remaining bit-time proof concerns the source parser, serialization and extraction, the width-sensitive cost of the vertex rational operations, edge construction and projection, and the adaptive threshold and price updates. The bound applies to runs that return a result.
