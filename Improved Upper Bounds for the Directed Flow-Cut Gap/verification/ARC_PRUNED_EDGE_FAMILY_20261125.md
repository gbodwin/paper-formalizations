# Pruning weights while preserving threshold demands

`RationalPrunedEdgeFamily.pruned` tests each proposed zeroing of an arc against the original rational threshold demands. The final weights preserve exact membership in the original demand list. Setting any remaining positive arc's weight to zero would lose at least one original threshold pair.

For a nonempty graph, the uniform family uses the number of retained positive arcs, with a minimum of one. Every cut separates the original threshold demands. Its arc marginals are bounded by 8 times the original length times the exact global factor at the original total weight. If at most as many positive arcs remain as there are vertices, the vertex-count horizon holds. The theorem supplies the original positive-arc bound when that count stays large.

The exact factor routine enumerates valid cuts and keeps the inclusion-minimal cut inequalities for its feasibility test. Nonnegative prices make every other cut inequality follow from one of those retained. `leastMinimal_eq` proves equality with the original exact instance factor, and `familyFor_reference` lifts that equality to the same uniform family construction. The cut enumeration is exhaustive.

The literal sampler proves the exact unread suffix, original-cut validity and bounded-rejection law. The executable example uses a length-one path with redundant light loops. It checks that the batch trimming test rejects while arc-by-arc pruning preserves the path as a threshold demand.

The executable run retained two of five positive arcs. It kept two of 24 cut constraints and computed the exact instance factor 1. The uniform family used 25 cuts on the pruned weights and 81 on the original weights. The sample used five literal bits and preserved its unread suffix.
