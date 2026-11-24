# Endpoint-safe vertex threshold and literal-tape sparsest cuts

The executable entry takes a Boolean adjacency matrix, rational vertex
lengths and prices, and a vector of demands. For each demand the binary
shortest-path routine assigns zero cost to departure from the source.
Every other traversed departure charges its original vertex length.
Lean proves exact agreement with internal-vertex distance, including
unreachable and self demands.

The harmonic selector chooses a positive attained threshold when the
finite distance sum is positive. The routine divides the lengths by
that threshold, keeps prices, and executes either vertex rounding mode
on the original tape. A returned cut separates at least one original
demand under the internal-vertex convention. With the stated budget,
the positive branch returns the exact unread suffix. An unreachable
demand gives the empty cut with the entire tape. All-zero finite
distances produce a separate result.

For distinct demand pairs and a positive selected threshold, the ideal
expected-sparsity bounds use the harmonic factor in size mode and its
power three halves times the square root of normalized mass in mass
mode. The finite fair-tape law is exact for the bounded draw tree.
Given a positive ideal sparsity scale B, the actual positive branch
exceeds 2B with probability at most one half plus the accumulated
finite draw error `drawBound n · 2^(-T)`.

The fixture ignores positive endpoint weights in a three-vertex path.
It computes a distance and threshold of one half and checks that both
modes cut the internal vertex, preserving the unread tape. It also
checks the distinct unreachable and finite-zero results.

The runtime entry uses supplied rational lengths. Computing the vertex
fractional optimum, high-confidence amplification, and complete
deterministic bit cost remain open.
