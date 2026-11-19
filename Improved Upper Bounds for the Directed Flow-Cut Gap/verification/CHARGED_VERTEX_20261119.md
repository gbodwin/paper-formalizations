# Charged execution of the two vertex modes

`ChargedVertexModes.run` takes the original typed rational graph, a tape,
and the requested confidence exponent. The physical fractional dispatch
executes once. Its retained output is read back and used in the same
rounding program. `ChargedVertexModes.run_value` proves equality of the
cut and remaining tape on every finite tape, including failure on tapes
too short for the draws encountered.

`PreparedIntegerController.bitTree_value` proves that the counted
dictionary, mask, initial mass and parameter preparation feeds the same
integer controller. The uniform, mass and size rounders preserve the
same bounded tree. `ChargedCutSelection.best_value` and
`ChargedAmplification.tree_value` retain the earliest candidate on a
tie, first among cover rows and then across repeated trials. Every
executed round incurs its charge, including rounds whose output loses.
One rejection limit is shared across the entire bounded execution.

`ChargedVertexModes.run_complete` supplies a valid solution or exact
infeasibility result, the unread tape, and the bounds on physical
dispatch, readback, and rounding with selection. It requires the
existing polynomial length of the random tape. The local price bound
includes padded stored bits. `ChargedVertexModes.budget_le` gives a
polynomial in the vertex count, stored price width and confidence
degree for the modeled word operations and binary pricing charges.
`ChargedVertexModes.run_fairTape` proves the same output law on the
finite fair tape, transferring the existing approximation and
confidence guarantees.

`AdaptiveWidthEnvelope.family_polynomial_reads` bounds the fair-bit
reads of the calibrated edge family using the width of the original
stored weights, the fixed multiplier's encoding, and the requested
confidence degree.

The physical dispatch and readback retain their own cost model. The
bound starts at typed input and accounts for instrumented rounds and
price selection. Input serialization and typed assembly, confidence
metadata, and the optimizer's bit and storage costs need a joint
fixed-instruction runtime proof. The near-linear horizon at the sharp
original-weight rounding factor also remains open.

The full library gate checks the module index, all owned declarations
and their dependencies, and the complete project kernel replay. The
additional gate strictly elaborates the new sources and runs the
prepared integer and composed vertex fixtures. The composed fixture
checks the actual zero-demand physical entry point, both modes on a
positive cover row, stable ties at both selection levels, and the
behavior on a short random tape. Its optional `--positive` case
runs the positive physical dispatcher, reads nine retained rows, and
feeds that one readback into both charged modes.
