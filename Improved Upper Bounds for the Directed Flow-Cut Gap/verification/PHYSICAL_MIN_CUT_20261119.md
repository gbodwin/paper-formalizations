# Fixed maximum-flow loop and exact minimum-cut output

`ResidualFlowStepProgram.physical_step` builds and searches the residual
matrix and gives the returned nonempty path directly to the table updater.
It preserves the original table address when search returns an empty path.
`ResidualFlowLoopProgram.physical_loop` repeats the step on each returned
table, spending exactly one unary budget cell for each augmentation. The
cut-budget invariant proves that an exhausted budget cannot leave an
augmenting path. The terminal table represents a maximum flow.

`ResidualCutProgram.physical_cut` builds the residual matrix of the supplied
flow, runs the full backward search and marks vertices missing from the
returned code table. `ResidualMaxFlowCutProgram.physical_min_cut` gives it the
actual table returned by the loop. Its 1,624-slot program returns the exact
mask of the reference solver's largest minimum cut in numerical vertex
order, with the same result for every reference enumeration. The tape is
unchanged and the bound includes the halt.

The stored entry fields include the feasible starting flow, capacities,
complete pair list, vertex labels and unary cut budget. The bound is
polynomial in the represented widths, the number of vertices and the unary
budget. Constructing those inputs from the candidate data and using the mask
in the full rounding controller are separate obligations.

Three fixtures run the fused step, the loop, the cut scan and the complete
program. They cover a three-augmentation zero start, an already terminal
flow with zero fuel, and a reverse-path cancellation. The first two return
`[true, true, false]`, including a vertex that has no path to the sink and
is unreachable from the source. The reverse-path case returns
`[true, true, true, false]`.
