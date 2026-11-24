# Measured binary arithmetic for edge and vertex covering

`MeasuredConcurrentCover.edgeRun_value` and `vertexRun_value` identify the
complete decoded state with the existing multiplicity cover at every iteration
on the corresponding typed input. The state includes the current weights, best
normalized weights and their price, total flow, and loads on each resource. The
pivot preserves the first minimizer of price divided by path multiplicity. A
stopped iteration checks the objective and runs no graph oracle.

`MeasuredConcurrentCover.edgeRun_charge` and `vertexRun_charge` bound the
returned charges from the input price width, graph size, demand count, and
iteration count. `MeasuredMultiplicityCoverBounds` bounds raw numerator and
denominator fields and the accumulated charge for initialization, multiplicity
updates, flow and loads, normalization, and objective tests. The graph charge
includes the reached binary shortest-path calls and the counted pivot divisions
and comparisons. For vertex cuts these searches still exclude the endpoints of
each demand. The existing covering horizon is three times the square of the
resource count, with one resource per vertex in the vertex solver and an array
of vertex pairs in the edge solver.

The graph fixtures compare all five decoded fields with the existing routines
and check that a stopped edge iteration adds no oracle work. The charge theorems
cover the named binary operations. Path projection, canonicalization and graph
storage, budget preparation and selection, and tape rounding have separate cost
obligations for a full bit-time bound.
