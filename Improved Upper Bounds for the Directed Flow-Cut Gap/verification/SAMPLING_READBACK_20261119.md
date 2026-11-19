# Heap readback and binary sampler charges

[PhysicalSourceReadback](../DirectedFlowCutGap/PhysicalSourceReadback.lean)
runs the cached physical dispatcher and then follows the binary pointers
in its terminal heap. It returns the same plan as the certified typed
reader. The exact lookup charge is the sum of the reference interpreter's
lookups. Its bound is polynomial in the original encoded input length.
The typed conversions, output allocation, and rounding have separate
costs.

[BinaryDrawTreeExecution](../DirectedFlowCutGap/BinaryDrawTreeExecution.lean)
executes finite draws with the Boolean-list bounded-rejection routine.
The projection equals the established lowered tree, preserving the bit
requests, rejection defaults, and order. The proved charge includes
binary word generation, comparisons, and trial counters.

[RetainedBinarySampler](../DirectedFlowCutGap/RetainedBinarySampler.lean)
uses that binary sampler in the actual counted controller. With the
computed initial demand mask and the algorithm's restart and epoch
parameters, the hard branch has a polynomial bound on its declared
word charges and modeled binary sampler work. The factory and mask
setup are outside this bound. The full controller storage and address
lowering remains open.

[EncodedBinarySampling](../DirectedFlowCutGap/EncodedBinarySampling.lean)
applies the sampler charge to the repeated vertex and edge solvers.
Both size and mass modes have a polynomial sampler-operation bound.
The projection gives exactly the established amplified tree. The other
deterministic operations in the outer solver retain their own scopes.

The charged sampler fixture takes both rejection defaults on its
actual permutation and cell tape. The charged readback fixture follows
the actual physical self-demand output and a separately built positive
heap. The larger physical fixture compares all nine ordered states from
the original three-vertex source and feeds those actual rows through
both rounding modes.

[Scoped verification workflow](../../.github/workflows/flow-constructive-rounding.yml)
