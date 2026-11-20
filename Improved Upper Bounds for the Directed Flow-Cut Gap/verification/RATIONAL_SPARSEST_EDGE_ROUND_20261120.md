# Rational sparsest-cut threshold and edge rounding

The executable entry takes a directed adjacency matrix, rational edge lengths,
rational prices, and a retained vector of demanded pairs. It calls the binary
shortest-path oracle to compute exact rational distances.
`RationalSparsestEdgeThreshold.choose_spec` distinguishes an unreachable demand,
all finite distances zero, and a positive attained harmonic threshold.
The score is the threshold times the number of demands at or above it.
Equal distances are counted separately for distinct demand pairs.

`RationalSparsestEdgeRound.run` passes the scaled lengths and original
prices to the two available rounding modes. The mass mode and the size mode are
selected through the mode argument. A cut returned by either mode contains only
original arcs and separates at least one original demand. The unreachable case
returns the empty cut and preserves the entire tape. The all-zero case returns
its own result. `round_reference` matches the entire cut and unread tape against
the existing tree interpreter. `round_fairTape` identifies the exact finite
fair-bit law, and `round_complete` proves termination with the unread suffix
once the explicit budget is available.

`RationalSparsestEdgeExpectation.size_uniform` and `mass_uniform`
bound expected sparsity under the ideal round at that computed threshold.
The distinct-demand condition identifies vector indices with the mathematical
demand set. The bounds use the harmonic factor, respectively its power
three-halves and the square root of normalized mass.

The native fixture checks a selected length of one half, rescaling to one,
unchanged price, two tied distances, an unreachable pair and a zero-length
self path. Both positive original one-arc executions return the expected cut
with the same unread tape.

The proof accepts supplied fractional lengths. The polynomial optimizer,
the vertex executable threshold entry, and the quantitative approximation
guarantee for the finite fair-tape solver remain open.
