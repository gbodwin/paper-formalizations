# Binary edge preparation

`PhysicalBinaryEdgeWire.edgeWithCost` reads the original edge source,
converts the actual stored prices, and runs the edge solver through the
physical fractional dispatcher with binary rounding on each returned row.
`edge_complete` proves validity and the exact remaining tape for every
accepted source with a sufficient tape. `PhysicalAmplifiedBinaryEdge.run_observe`
and `run_fairTape` identify the output and tape law with the established
edge solver in both modes.

`BinaryEdgeGadget.build` uses binary dyadic comparisons, builds the
dyadic weight words, and sums each retained edge price with the
binary rational addition routine. `build_value` identifies the exact
gadget, including the raw numerator and denominator fields. `fields_fit`
bounds those fields from the observed line cover rows and original
cost widths. `PhysicalBinaryEdgeWire.edge_wire_polynomial` bounds the
returned counters in the supplied source length and the numerical
confidence exponent.

The counters include measured binary scalar operations and conservative
allowances for graph and index operations. The earlier integer cutoff
gate remains in the word model. The adaptive rational updates and
remaining graph serialization and conversion costs have separate
verification scope.

The executable checks compare the binary gadget with the retained
construction, round a positive actual line-graph input row, and run
the literal edge entry on padded prices, a self-demand, and malformed input.
