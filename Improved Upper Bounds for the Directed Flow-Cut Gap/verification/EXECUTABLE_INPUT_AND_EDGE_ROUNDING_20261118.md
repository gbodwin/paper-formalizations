# Source-table input, amplification, and edge rounding

This continuation starts from the typed vertex solver and the preserved
median repair. It uses the existing source-table format for a Boolean
adjacency matrix, an ordered demand list, and padded nonnegative rational
vertex costs.

- `EncodedVertexInput.parse_encode` gives the typed round trip.
  `EncodedVertexAmplification.sourcePolynomialBitTree_encode` identifies
  the repeated solver reached from those exact source bits. Decoding
  rejects incomplete tables, trailing bits, zero denominators,
  nonsquare matrices, and out-of-range demand endpoints.
- `EncodedAmplification.samples_law` identifies the actual repeated
  sampler with the ideal product distribution. Selection compares exact
  rational prices and returns one of the samples. The lowered tree
  preserves valid support, including its rejection defaults.
  `EncodedVertexAmplification.polynomial_failure_le` bounds failure by
  `(max 1 n)^(-κ)` at twice any positive bound on the ideal expected
  cost. `EncodedAmplification.bitTree_within` bounds fair-bit reads in
  terms of a draw count and width for the ideal sampler.
- `EncodedEdgeGadget` builds arrays for the dyadic gadget using supplied
  rational edge weights and costs. `EncodedEdgeRounding` pulls back
  actual edge sets on every supported result of the bounded-bit program.
  Its size and mass theorems bound the ideal expected price using the
  supplied fractional weights.

The CI workflow binds its checkout, strictly checks these sources,
replays the listed modules with the official Lean checker, audits
logical dependencies and reports compiler recursion declarations in a
separate inventory. Execution fixtures cover the source encoding and
rejections, a fair-bit draw that rejects, the minimum selection, the
remaining input bits, and an edge that requires cutting.

The machine-level source-to-rounding splice, an initial fractional
solver for edge costs and demands, the full bit-operation bound, and
the exact-weight weak-decomposition oracle remain open.
