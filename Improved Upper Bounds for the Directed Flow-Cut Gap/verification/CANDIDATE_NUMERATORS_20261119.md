# Physical candidate numerator solver

`CandidatePreparedSolverProgram.physical_prepared_solver` checks a fixed
2,386-slot reference machine under the terminal-inclusive bit-operation
model. It constructs the search configuration and budget, computes the
retained minimum cut, and consumes the returned cut pointer on the same
heap. The decoder uses the original removal mask and grid word. For each
vertex it counts two consecutive threshold blocks. It returns the original
grid word for a removed vertex and the difference of the counts otherwise.
The ordered word values equal the retained candidate numerators. The
theorem includes the original tape, the original heap prefix, and the
charged terminal attempt.

The entry point assumes a width-bounded capacity matrix for the candidate
and represented vertex count, removal mask and grid. Its mathematical
premises include positive grid size and candidate feasibility. Matrix
construction and the surrounding rounding controller remain open at this
checkpoint.

`CandidatePreparedSolverSmoke.lean` checks four decoder cases, including a
padded grid, a removed vertex, and an empty result. A separate three-vertex
path uses the direct candidate capacity matrix and a binary grid size of one.
The independent residual trace identifies four unit augmentations at
budget six and returns numerators `[0, 1, 0]`. The fixed machine returns the
same numerators in 39,309,836 instructions and pays 13,518,428,763,757,158
modeled operations including the halt. The fixture checks the exact
instruction count, output, stack, original tape, and heap prefix.

The branch inherits the full-library axiom audit and official kernel
replay. It adds strict builds for the seven numerator modules and executes
the candidate fixtures under the reference simulator.
