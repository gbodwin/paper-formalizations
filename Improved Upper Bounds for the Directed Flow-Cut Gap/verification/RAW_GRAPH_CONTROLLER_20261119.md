# Original-input packing and computed controller budgets

`RawGraphInputStore.prepare` installs the actual adjacency rows and binary size, threshold, and trial words by paid append-only allocations. Its proof derives the exact cell count, address-width bound and cubic preparation charge from these words. The program takes an original Boolean graph with a positive integer threshold and a binary word giving the number of rejection trials per draw.

`PhysicalControllerControls` computes the integer restart ratio and the cubic limit from the vertex-count word. The geometric counter starts with the ratio and counts its powers through the cubic limit. Each multiplication has the fixed ratio as its first operand, which gives a linear bound on the width growth across iterations. The stored result has the exact restart and epoch fuel used by the paper. The controller allocates its actual trial spine from the binary word.

`RawGraphControllerProgram.guarded_cut` proves an explicit charged run of a fixed 26,704-slot instruction table. It packs the controls, initializes the original graph, executes the guarded tape controller, and returns the physical cut pointer. The proof covers success and the unread source and shows rejection when the model requires further bits. `RawGraphControllerLaw.fairTape_law` identifies the actual machine's output distribution on a finite fair tape with the exact bounded-rejection law.

The executable checks include a zero-vertex control computation and a three-vertex computation with a padded trial word. On the two-vertex complete graph, the prepared input costs 11,209 modeled operations. The joined guarded run completes in 7,848 instructions, charges 674,114,657 modeled operations, returns the actual cut pointer and preserves the literal tape. The separate positive epoch fixture exercises a live draw, cut and refresh from its represented cache.

The trial word is an input. The worst-case charge stated here uses the explicit controller bound. The polynomial envelope in original encoded width and the complete weighted and amplified dispatch are separate proof obligations.
