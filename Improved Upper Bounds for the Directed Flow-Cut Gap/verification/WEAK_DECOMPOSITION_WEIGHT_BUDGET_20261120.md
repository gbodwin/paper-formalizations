# Uniform families at the original weight budget

`ExactFlowCutGap.efg_mono_weight` pads the total on a zero-price self-loop. A simple path never uses that loop. The oracle at the larger total gives cuts with the original support, threshold validity, and price bound. This proves the direction of monotonicity that the weight-budget argument uses.

`ExactFlowCutGap.edge_uniform_at_weight_budget` uses the exact original factor α and any integer `k ≥ n` with `k ≥ nW`. Its horizon is at most `ceil(2 k log(4 α k W + n²)) + 1` and its marginal bound is `16 α w(e)`. A small total mass of light edges allows a penalty argument on the original graph. Otherwise their removed mass pays for the rescaling required by simple paths. The rescaled instance fits the original total, and its cuts cover the original threshold demands. Choosing `k = n ceil(max(1,W))` gives a near-linear horizon for bounded `W`.

`ExactFlowCutGap.edge_uniform_of_clipped_mass` gives the near-linear horizon and marginals at most `8 α w(e)` whenever dropping tiny weights, doubling the remaining weights, and clipping them to one fits the original total. This applies when `W` is at least the number of actual edges. `ExactFlowCutGap.vertex_uniform` gives the vertex family at the original factor without a weight floor.

`ExactFlowCutGap.edge_uniform_at_preprocessed_weight` formalizes a near-linear family for every original edge-weight vector with the oracle factor evaluated at the total after preprocessing. Its cuts meet the original threshold and its marginal bound uses the original edge weights. This factor can differ from the exact factor at the original total.

`BinaryEdgeProjection.matrix` computes the positions in a flat matrix with charged binary arithmetic. The edge solver decodes its original prices through this routine, and the original weak-cut wire moves its packed weight fields through the same routine. These operations preserve row order and the accepted cut and unread tape. The composed counter bounds include their actual charges. Width-sensitive simulation of the structural word operations and the unrestricted near-linear uniform edge horizon remain open.
