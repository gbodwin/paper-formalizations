# Measured binary preparation for the guarded edge sampler

`MeasuredBudgetRescaleEdgeFamily.prepare` classifies the original arcs and sums the original, saturated and subunit components as unreduced binary fractions. It subtracts the reserved integer from the original budget, divides by the subunit total when positive and caps the multiplier at two. It reads and emits typed matrix cells in the original order.

`rescale_weights` proves that each output fraction has the same value as in the previous rescaling. The binary guard checks the original pairs against those weights. It skips the second shortest-path search for pairs already close and stops at the first lost demand. `prepare_preserves` proves the guard makes the same decision as the previous sampler.

`rescale_bounds` gives the maximum output word width and a preparation charge bound for any input width bound. `prepare_paid` also covers the threshold searches and comparisons. These bounds use the binary arithmetic and retained-array operation models. The factor search, family construction and complete addressed-machine execution have separate runtime obligations.

`family_reference` matches the entire ordered family, including the pruning fallback. `draw_reference` matches the returned cut or rejection, the recorded sampling charge, and the exact unread tape. The original factor and the conditional vertex-count horizon apply as before. The horizon requires a successful preservation check or at most $n$ positive arcs after pruning on a nonempty graph.

The native check emitted the unit-length leg as $1080/1080$, charged 41,744 preparation operations and matched the reference six-bit draw. The rejected fork charged 57,909 operations and used the same pruning fallback. Empty preparation charged 85 operations and yielded the singleton empty cut.
