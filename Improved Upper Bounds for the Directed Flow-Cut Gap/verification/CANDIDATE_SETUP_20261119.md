# Candidate search configuration and cut

`BinaryLabelRangeProgram.natural_range` reads a stored binary count and
builds the canonical word list in numerical order. `WordPairProductProgram`
builds the full ordered Cartesian product by reusing the word addresses.
`LastTwoWordProgram` returns the existing final two word addresses.

`CandidateInputConfigurationProgram.physical_input_configuration` computes
the network size from the stored vertex count and grid size. The 299-slot
program enumerates the labels and pairs and packs the exact search
configuration with the candidate's artificial terminal labels. The bound
accounts for the represented input widths and the numerical network size.

`CandidateConfiguredCutProgram.physical_configured_cut` passes that actual
configuration to the closure solver. Its budget uses the same stored grid
word and the original removal mask. The 2,177-slot program returns the
exact retained candidate cut under the supplied feasibility and capacity
representation premises. The heap prefix and tape are preserved, and the
charge bound includes the halt.

Eleven executable cases cover empty and padded ranges, ordered products,
terminal address selection, and the complete candidate cut. For two
vertices and grid size one, the configuration has 26 canonical labels
and 676 ordered pairs. The prepared candidate fixture compares all 26
returned flags with the retained solver and checks the exact halt. It
selects 21 vertices after 2,297,185 successful instructions and pays
35,351,982,920,325 modeled operations. The fixture has zero closure budget.

The capacity matrix is still stored at entry. Constructing the entire
matrix from the original graph and decoding the cut into the candidate's
numerators are separate obligations.
