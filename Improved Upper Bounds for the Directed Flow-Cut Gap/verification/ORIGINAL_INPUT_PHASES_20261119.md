# Counted input parsing and prepared adaptive demands

The physical vertex and edge entries use the counted parser. The framing pass reconstructs the exact original words, tables and remainder. It bounds its charge on all bit strings. The assembly pass validates rational denominators, matrix dimensions and demand endpoints. It preserves stored padding and has a cubic charge bound in the supplied source length.

`PhysicalOriginalInputCompleteness.vertex_complete` and `.edge_complete` establish valid output and the exact unread tape on any accepted input with a sufficient tape. `PhysicalWireCostEnvelope.vertex_wire_polynomial` and `.edge_wire_polynomial` include the parser and the previously measured solver counters. These bounds use the total original source length and the numerical confidence exponent, including on accepted padded encodings.

`PhysicalPreparedEdgeFamily.run` computes the original threshold-demand list once using measured binary shortest paths and comparisons. It reuses this list for every adaptive query. Its full family and unread tape agree pointwise with the verified adaptive solver. The threshold charge is polynomial in the vertex count and the original stored weight width.

`ChargedEdgeDyadicLabels.label` computes the original dyadic label using charged comparisons on actual binary words. Its scope covers each label. The full edge gadget construction, its output projection, vertex reduction bit widths, and adaptive price updates remain separate runtime obligations.
