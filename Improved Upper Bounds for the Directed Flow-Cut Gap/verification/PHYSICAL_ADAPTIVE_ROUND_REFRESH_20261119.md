# Selected adaptive round followed by cache refresh

`BinaryProductOrderProgram.natural_order` proves the result of computing a product and comparing it with a stored word. `AdaptiveGatesProgram.natural_gates` uses actual padded word inputs to return the retained integer ready and active flags. The test includes a padded zero optimum, a failed ready test, and both sides of the activity threshold.

`AdaptiveRoundRefreshProgram.physical_round_refresh` builds the cut and update argument records from the cached state, uses the selected original pair and grid table to run the midpoint cut, and passes the actual resulting masks to the refreshed candidate family and optimum computation. The resulting cache contains the exact integer sampled round and exact refresh. The theorem preserves the tape and heap prefix and accounts for successful instructions and the halt.

The entry point receives a represented selected pair, valid current state, original grid table, and graph and scalar representations. The iteration that selects pairs and tests their membership in the current demand mask still needs physical composition. Stabilization, full controller initialization, and the original-input bit-time bound remain separate obligations.

The composed fixture starts with two vertices, an edgeless graph, and one represented active demand. Its literal fair tape leaves a two-bit suffix. The fixture takes the pair and cell-table addresses from the actual guarded epoch output. The selected round clears the demand, and the actual refresh returns a shared zero row at each of the four positions and optimum zero. The composed round and refresh complete 2,029 instructions and charge 41,790,635 modeled operations while preserving the suffix.
