# Charged edge projections and an exact-weight uniform family

`BinaryLineLabels.prepare_value` and `prepare_paid` identify the actual line adjacency, prices and ordered demands and bound their recorded charges. Adjacency uses the charged binary comparison on typed vertex labels. Nonedges and ports retain their original interpretation.

`BinaryEdgeProjection` computes the arc positions with binary multiplication and addition. It measures the transport of returned fractional rows, the scan from selected gadget labels to original edges, and the conversion of line masks and infeasibility witnesses. The physical edge solver and paired price selection call these routines. The equality theorems preserve the selected cut or infeasibility witness and the unread random tape. `PhysicalBinaryEdgeCost.edge_polynomial` and `PhysicalPairedEdge.wire_polynomial` bound the resulting counters.

`WeakDecomposition.edge_family_of_small_mass` works with the original graph, weights, and threshold demands. With cutoff `1 / (4 α k)`, it assumes that the sum below or at the cutoff, multiplied by `α`, is at most `1/4`. The original oracle then supplies cuts that avoid the tiny edges, using a penalty argument. The horizon is `ceil(2 k log(4 α k W + n²)) + 1` and the marginal bound is `8 α w(e)`. The premise holds when at most `k` edges carry positive weights below or at the cutoff. `ExactFlowCutGap.edge_uniform_of_small_mass` specializes to `k = n` and the least integer factor at the unchanged total `W`.

The recorded edge costs combine binary arithmetic with structural word operations. A width-sensitive simulation of those operations remains open. The near-linear uniform family still has an explicit small-mass premise, and the general exact-weight family retains its quadratic horizon.
