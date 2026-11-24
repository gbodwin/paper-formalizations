# Measured budgeted covers and the original positive-arc horizon

## Budgeted covering computations

`MeasuredBudgetCoverCandidate.edge_value` and `vertex_value` reproduce
all stored numerator and denominator bits of the prior candidate
for each input price-and-mass budget. The measured algorithm reprices
with two binary divisions and a sum. It uses binary Euclid to convert
to the canonical representation consumed by covering and by the
endpoint-excluding vertex and edge shortest-path routines. The final
scaled lengths use the same canonical representations as the previous
candidate functions.

The corresponding charge theorems cover the price conversion,
repricing, arithmetic and binary shortest-path and pivot calls of the
actual covering recurrence, and the emitted lengths. The input
budget widths control the widths of the repriced values. The
covering step bound uses the existing fuel. The candidate-list
proofs give the exact same ordered list for both graphs and bound
the sum over all generated pairs. For vertices, the proof also
bounds the list length and the price and mass budget widths directly
from the input. Costs of graph storage and path projection, grid
production, final candidate selection and tape rounding require
separate bounds.

## Original total weight

`ExactFlowCutGap.edge_uniform_at_original_positive_arc_count` uses
`max 1` of the number of actual arcs with positive weight as the
scale in `smallMassHorizon`. Zero-weight arcs do not contribute to
the small-edge penalty budget. For a nonempty vertex set, every
supported cut separates the original threshold demands and the
edge marginals are bounded by eight times the original least integer
factor times the original edge weight. This yields the vertex-count
near-linear horizon when the positive-weight arc count is near-linear,
including graphs with many additional zero-weight arcs. The unrestricted
dense positive-weight case remains open.
