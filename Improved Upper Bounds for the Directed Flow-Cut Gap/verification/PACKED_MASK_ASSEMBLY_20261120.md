# Measured packed cut-mask assembly

The hard rounding path recovers a bitword from the original packed controller. `GuardedFuelFreeRounding.hard_mask_copy` proves that every returned mask comes from a word of exactly the input graph dimension. The measured constructor preserves bit order and assembles the typed array within the existing mask-copy allowance. `GuardedFuelFreeRounding.meets_old_entry` retains its original result and total recorded-work comparison for every literal tape.

`MaskBoundaryAssembly.copy_instructions` follows the actual array-copy constructors, including repeated destination allocation. It proves the trace length and bounds the number of newly allocated cells. `copy_address_size` bounds the number of bits for each allocated address as a function of the initial cells and the graph dimension. `BinaryMaskPrefix` uses binary decrement to inspect only the requested output positions. On shorter or longer input, it agrees with the earlier padding and truncation behavior.

The executable checks keep the singleton's returned cut, tape and total packed-run charge. Separate copy cases exercise padding, truncation and the empty mask. The complete width-sensitive bound still requires a proof for the rest of the source-to-cut execution.
