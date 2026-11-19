# Fixed candidate closure cut from the removal mask

`IntegralFlowRelabeling` transports feasible signed flows and residual paths
between the closure nodes and their canonical numerical indices.
`ClosureMaxFlowRefinement.reference_mask` identifies the exact retained cut
using uniqueness of the largest minimum source side. The isomorphism is
used in the proof. The physical program runs on numerical labels.

`ResidualZeroTableProgram.physical_zero` creates a table with a single shared
canonical zero amount and preserves the original capacity pointers.
`ResidualZeroMinCutProgram.physical_zero_cut` starts from that table and
converts a stored binary budget into unary fuel for the minimum-cut loop.

`CandidateBudgetData.budget_exact` proves that the closure budget is twice
the grid size times the number of unremoved vertices. The 157-slot budget
program reads the actual mask, counts its false entries, multiplies by the
grid size, doubles and trims the resulting word.
`CandidateBudgetCutProgram.physical_budget_cut` passes that returned word
in the same heap to the 1,689-slot zero-start solver. The full 1,862-slot
program returns the exact retained candidate cut in numerical label order.
It preserves the original heap prefix and unread tape and includes the
halt in its charge bound. The bound uses the vertex count, grid size and
stored widths.

The capacity table and search configuration are represented entry fields.
Producing those fields from the original graph, converting the returned
cut mask into candidate numerators and composing the full rounding
algorithm remain separate goals.

Ten executable cases check positive and zero budgets, canonical words from
padded inputs, empty and fully removed masks, original capacity addresses,
the shared zero amount, and complete cuts. The fused cut fixtures are small
closure networks. The equality to the paper's retained candidate cut is
proved for all feasible candidates with the stated entry fields.
