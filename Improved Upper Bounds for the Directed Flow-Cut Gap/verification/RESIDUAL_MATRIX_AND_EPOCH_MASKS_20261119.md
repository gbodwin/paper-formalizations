# Residual adjacency and epoch draws from active masks

`ResidualCapacityProgram.residual_edge` executes a strict capacity test from
a stored canonical signed amount and a binary natural capacity. Its
magnitude-width proof uses both directed capacities and skew symmetry.
`ResidualRowProgram.physical_row` and
`ResidualMatrixProgram.physical_matrix` apply that test in the supplied
vertex orders and return the Boolean layout used by graph search. Lean
checks the unchanged tape, the original heap prefix, and the bit charge
including the halt. This entry assumes the amount and capacity table is
already represented.

`IntegralNetworkFlow.finiteResidualCut_eq_of_terminal` proves exact equality
of the executable cut for any two terminal flows and vertex enumerations of
the same network. Each equal-value separating cut is residual-closed because
every crossing slack is zero. The executable cut is the complement of
vertices that reach the sink, so it contains every optimum source side.

`RetainedEpochFromMasks.physical_epoch` counts the active demands
in the represented masks and generates the decreasing permutation bounds
and repeated grid bounds before running the guarded draws on the same tape.
The represented grid bound and shared trial spine are entry inputs. The
output contains ordered draw records, and Lean proves the exact index
projection, read count, unread suffix, and behavior on exhausted tapes.

The executable fixtures exercise reverse residual edges, saturated arcs,
binary padding, empty matrices, schedule construction, four consecutive epoch
draws, and tape exhaustion. Decoding the draws into an applied permutation
and levels, constructing and updating signed flow tables, executing residual
search and the optimizer loop, and composing these pieces into the full
solver remain open at this checkpoint.
