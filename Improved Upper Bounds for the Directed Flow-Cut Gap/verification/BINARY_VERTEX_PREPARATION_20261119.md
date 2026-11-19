# Binary vertex preparation

`PhysicalAmplifiedBinaryVertex.vertexWithCost` parses the original source and
runs the amplified vertex solver with measured binary rational preparation.
`vertex_complete` covers every accepted source with the original sufficient
tape bound. `vertex_fairTape` recovers the amplified law on independent fair
bits. `vertex_observe` identifies the output and unread suffix on each
literal tape with those of the established physical vertex solver.

- `PhysicalCoverWidthEnvelope.rows_width` gets each row's raw field bounds
  from the actual terminal fractional heap. `VertexReductionWidths`
  propagates field bounds through the capped weights, replicated input
  and uniform chain.
- `PhysicalBinaryVertexRounding.weighted_cut` and `size_cut` recover the
  original masks, unread tapes and earlier charges. The added counters
  include binary encodes and decodes, rational sums, products, divisions
  and comparisons, ceilings and the bounded cube-root search. The
  preparation reuses computed fields when it materializes the graphs.
- `PhysicalAmplifiedBinaryVertex.vertex_wire_polynomial` bounds the
  parser and returned counters in the supplied source length and the
  numerical confidence exponent. The proof applies the arithmetic bound
  to rows actually read back from the dispatcher.

The integer cutoff gate still uses the earlier word arithmetic. Graph
construction and conversions outside the measured binary routines retain
their earlier cost scopes. The edge gadget and adaptive price updates are
separate obligations. The polynomial bounds this modeled counter rather
than Lean's native compilation or execution time.

The executable gate compares a positive weighted instance, a zero objective
and a heavy vertex with the retained solver. It also runs the binary
preparation from a positive encoded three-vertex path. The kernel and
axiom gates run from the full library import and bind the reference closure.
