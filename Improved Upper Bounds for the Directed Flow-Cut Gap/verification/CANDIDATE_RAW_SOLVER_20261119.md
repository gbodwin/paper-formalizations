# Physical candidate solver from the stored graph

`CandidateRawSolverProgram.physical_raw_solver` starts with the stored
Boolean adjacency rows, vertex count, removal mask, grid size, cap word,
and canonical terminal words. A fixed 3,797-slot program constructs the
tagged threshold descriptors, counts the budget, builds the four capacity
words, and assembles the complete capacity matrix in numeric vertex order.
The cell program computes the relation flags and terminal pins from those
descriptors and the original graph and mask.

The returned matrix address enters the minimum-cut computation on the same
heap. The decoder consumes the returned cut with the original removal mask
and grid word. Its ordered values equal the retained candidate numerators.
Positive grid size and candidate feasibility are premises. The proof
includes the preserved tape and heap prefix, the empty output stack, and
the paid halt. The instruction and modeled bit-operation bounds depend on
the numerical vertex and grid sizes and the stored input widths.

The fixture compares all 1,444 entries for each of two matrices. One uses a
two-edge path at grid one and the other a reversed arc, mixed removal mask,
and cap zero at grid two. The complete solver fixture starts with an edgeless
two-vertex graph and both vertices removed. It builds the 26-vertex closure
and returns both original padded grid words, with numeric output `[1, 1]`.
It executes 2,416,070 instructions and pays 41,811,859,950,604 modeled
operations including the halt. The enclosing candidate search and adaptive
rounding controllers are separate proof obligations.
