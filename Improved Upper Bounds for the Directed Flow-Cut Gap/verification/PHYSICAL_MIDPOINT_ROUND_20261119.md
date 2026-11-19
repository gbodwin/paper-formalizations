# Fixed-instruction midpoint cut and rounding update

Integer vertex rows use denominator-one fractions in the existing physical
shortest-path program. Lean proves that any recovered walk has denominator
one and that its numerator is the optimizer's integer distance. An absent
walk represents infinity. The fixed midpoint program takes those stored
optional walks and tests the actual binary integers. It includes the lower
boundary and excludes the upper boundary.

IntegerLevelVertexProgram executes recovery and the midpoint test for one
target. IntegerLevelCutProgram constructs the target context in the same
heap and scans all vertices in ascending index order. It returns the exact
mask from EncodedRoundingInput.cutFlags. The instruction bound uses the
width of the stored graph inputs and a bound on the recovered path costs.
The bound applies to each scan iteration as the heap grows.

PhysicalSampledRoundProgram.physical_round runs the midpoint scan and feeds
its returned mask directly into the retained mask and mass update. It clears
the represented selected demand, unions the newly computed mask with the
accumulated cut, and recomputes the current mass from the original count
words. It proves equality with the rounding controller's updated fields.
The 1,982-slot program preserves the tape and appends to the original heap.
Its polynomial charge includes the terminal instruction.

The entry state contains the selected pair and level, the corresponding
graph bundle and target-weight row, and the represented retained masks and
weights. The optimizer, construction of those inputs, fair sampling, and
complete fixed-instruction solver composition remain open.

The verification gate strictly elaborates all five new modules and executes
five native fixtures. They cover finite and infinite distances, midpoint
boundaries, the complete indexed mask, and a round that returns the expected
remaining demand, cumulative cut, and mass. The full library audit and
official kernel replay cover every imported project module and the root.
