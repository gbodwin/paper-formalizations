# Candidate capacities from binary threshold operands

`CandidateCapacityFlags.amount_eq_capacity` identifies each capacity in
the numbered closure network using the unit and barrier flags. The binary
words constructed from the closure budget represent the exact canonical
capacities and fit the width used by the fixed minimum-cut program.

The fixed port-adjacency routine reads the original stored Boolean matrix
and checks the extra source-to-sink diagonal using the actual binary
indices. The port-gap routine indexes the original removal mask and
uses the returned minimum of the grid and bound words. The threshold
routine reads stored levels and either checks descending order or checks
equality after adding the selected unsigned shift.

`CandidateCoreCapacityProgram.physical_core_capacity` combines the shift
test and word selection in a 208-slot instruction table. It uses the
actual shift address and the actual returned barrier flag. It preserves
the original heap and unread tape, and the charge bound includes the halt.
`CandidateTerminalCapacityProgram.natural_source` and `natural_sink`
identify the capacities computed by the separate 65-slot program. It
tests zero from the level word, computes the signed unit and terminal-pin
flags, and passes their actual returned addresses to the word selector.

The composed cell programs receive stored threshold descriptors, equality
or matching-port flags, the relevant shift or activity operands and the
budget-derived word table. The individual routines establish several of
those operands from the original matrix and mask. Joining every operand
producer to a single traversal of the entire capacity matrix and building
the search configuration from the original input remain separate goals.

The 43 executable cases cover every word-selector branch, padded thresholds,
both outcomes of reversed port adjacency, the diagonal port case, removal
mask lookup, gap capping and both terminal modes. Six core cells are checked
against the original closure capacity. One positive shifted cell returns 17
in 99 successful instructions and pays 201,808 modeled operations including
the halt. A companion shifted cell returns zero under the same bound.
