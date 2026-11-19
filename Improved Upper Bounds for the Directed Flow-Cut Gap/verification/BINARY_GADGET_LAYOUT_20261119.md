# Charged dyadic graph assembly

The original edge solver now collects the actual arcs once in row order. It
uses the same list to select retained label vertices and gather their prices.
The label scan stops at the first matching arc. Its endpoint and dyadic label
comparisons use measured binary words. The adjacency matrix charges each
reached comparison and original adjacency lookup.

`BinaryEdgeGadget.build_value` identifies the exact retained vertices, label
order, adjacency, weights, and raw price fields with the reference gadget.
`BinaryEdgeGadget.build_paid` composes the assembly charges with the prior
weight and price arithmetic bounds. Array access and list construction retain
their established word charges. The remaining outer operations include the
line-graph matrix and final cut projection.

The native fixtures cover the empty matrix and a three-vertex graph with a
self-loop, four actual arcs and mixed rational prices. They compare the entire
retained vertex order and matrix against the reference and check both raw
rational rows and the charge bound.
