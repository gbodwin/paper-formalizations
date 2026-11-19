# Guarded fair draws in the retained rounding epoch

A fixed program builds the binary word from the reached bit requests in
little-endian order. Bounded rejection uses the stored bound word and a
represented trial spine. The result record stores the accepted index
and a flag that identifies rejection exhaustion and the legal zero default.

The guarded interpreter checks the source tag before each request. Lean
proves that it returns the exact ordinary execution whenever every reached
request has a bit and returns absence on the first missing bit. The
additional modeled dispatch and tag work is charged. The checked result
agrees with the existing rejection tree, including the failure flag,
trial and read counts, and unread tape.

The 94-slot batch executes the supplied bounds in order and preserves
the draw records in that order. The epoch theorem specializes them to
the decreasing permutation bounds followed by one grid bound per active
demand. The actual configured bounds are canonical binary words. Lean
checks the exact projected index list, the remaining tape, and the read
count, or exhaustion, against the original retained epoch draw tree.

The entry heap represents both the bound table and a single shared trial
spine. Constructing those inputs, materializing the decoded permutation
and grid choices, and integrating the optimizer and the outer solver
remain separate obligations. The polynomial for this stage is in the
number and stored width of the bounds, the number of allowed trials,
and the initial heap and address bounds.

The native fixtures cover acceptance, rejection, the legal zero default,
zero trials, and exhaustion before and after a rejected word. An epoch
uses the two permutation draws and two grid draws, checks all four
records and the unread tape, and runs the short-tape and empty-set cases.
