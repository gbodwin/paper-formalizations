# Library and deterministic component verification

The generated `DirectedFlowCutGap` import includes the charged solvers,
their proved bounds, and all tracked modules under the library directory.
The library workflow checks that index, runs the axiom and dependency
audit over the whole import, and requires kernel replay of every module.
The source-to-cut workflow retains its own tests, including the checked
positive source trace.

[BinaryCutPriceSelection](../DirectedFlowCutGap/BinaryCutPriceSelection.lean)
computes each repeated cut's binary rational price once and preserves
the stable minimum selected by the amplified algorithm. Lean verifies
the additions and comparisons and bounds their modeled charge.

[BinaryAllocationTrace](../DirectedFlowCutGap/BinaryAllocationTrace.lean)
executes the reservation instructions with a binary bump pointer. The
ordered blocks and final pointer agree with the existing array storage
certificate. The proof bounds the pointer-addition charge for the actual
collection trace, including padded starting pointers. Filling the slots,
general address traffic, and executing the full rounding controller on
the fixed instruction set remain open.

The earlier exact GitHub run reached the expected physical stop and
timed out while checking the retained rows and cuts. The workflow allows
more wall-clock time for those checks. It still uses the same source
and forty-million-attempt limit for the positive fixture.
