# Indexed price selection in both original solvers

`BinaryCutPriceSelection.maskFieldsWithControl` reads each reached mask slot and reads a price slot when that vertex is selected. It constructs the same ordered fraction list as the earlier score. `minimumWithControl` uses that score once per reached cut and preserves the full winning record, including the first cut among tied prices and the original fee. Its new operations include binary accumulation of the comparison and score fees.

`PaidVertexAmplification.runWithPlanSelectionWork_reference` preserves the paid result and unread tape of the earlier amplification. Failed walks retain the work already spent. The selector is reached only after every requested sample succeeds. `runWithPlanSelectionWork_paid` bounds the new price work using the number of samples, the dimension, and the bit width of the earlier fee.

The corresponding original-source entry points are `PaidFramedVertexWire.vertexWithTerminalSelectionWork` and `PaidDirectEdgeWire.edgeWithTerminalSelectionWork`. Their reference theorems preserve the earlier output and phase records. The vertex entry adds price operations to its separate work field. The edge entry adds them to its paid scalar while preserving its boundary and framing records. The linked polynomial theorems cover every literal source and tape in terms of source length and numerical confidence.

The fixtures check a nonempty tied minimum, a completed amplification, both original empty graph entries with an unread suffix, and a trailing vertex source that incurs zero selection work. The claims cover the modeled operations in these entries. General structural bit time remains open.
