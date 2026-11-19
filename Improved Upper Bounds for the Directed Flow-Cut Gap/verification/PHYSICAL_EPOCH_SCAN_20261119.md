# Physical fair-tape epoch and scan

`EpochScanProgram.physical_scan` reads the retained ready and active gates and the live demand flag for the head of the stored order. If the head is current and the cache is active, the program runs the physical midpoint cut, updates the masks and mass, and refreshes the candidate family before advancing. It stops when the order is empty, the cached gate fails, or the head demand has been erased. `EpochScanData.scan_exact` identifies the result with the original integer scan and its exact refreshed cache.

`PhysicalEpochScanProgram.physical_epoch_scan` starts with the stored graph parameters, retained cached state and unary trial cap. Its fixed 7,789 slots load the current mask and immutable original-label dictionary, draw the permutation and grid cells from the literal fair tape, and scan the returned order and cell table on the same heap. It preserves the unread suffix and the entire initial heap. Its explicit bound covers instructions, heap growth and interpreter operations including the final halt and guards. The mass widths used by the gate bounds follow from the actual retained rows. The theorem takes bounds on the represented initial weights and epoch words.

`PhysicalEpochScanProgram.physical_epoch_rejected` proves rejection for any evaluator fuel and accumulated charge if the sampler exhausts its tape. It witnesses a prefix requesting more bits than are available. The subsequent scan is unnecessary for this rejection proof.

The executable fixture on the path 0 → 1 → 2 starts from a valid cache for one active pair. The full program uses the literal tape to cut vertex 1, clears the demand, returns current and optimum zero and preserves the two-bit suffix and runtime record. It completes 12,796 instructions and charges 1,003,581,423 modeled operations. A separate run with a one-bit tape is rejected. The isolated scan also checks an empty order, an unready cache and a stale head.

The entry point is a represented retained cache for one epoch. The remaining controller obligations include its initialization, stabilization, repeated epochs, and a composed deterministic bit-time bound from the original stored input.
