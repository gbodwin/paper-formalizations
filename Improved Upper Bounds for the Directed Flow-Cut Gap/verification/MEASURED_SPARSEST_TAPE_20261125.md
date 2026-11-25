# Paid execution of the budgeted sparsest-cut solvers

`MeasuredPaidSparsestRound.edge_value` and `vertex_value` relate the typed rational solvers to the earlier amplified solvers on every supplied tape. The observable result includes the original-graph cut and exact unread suffix, or exhaustion. The equality transfers the earlier correctness and fair-tape guarantees with their stated demand and tape hypotheses.

`MeasuredCutSparsity` computes each sampled cut's exact original price per separated request. It checks each indexed request. In the vertex model, the request's endpoints are retained. `MeasuredTapeSelection` charges for successive attempts and the binary accumulation of their fees. It keeps the first equal-score cut and skips selection if an attempt exhausts the tape. The edge runner builds the gadget once and projects successful samples back to original arcs before scoring.

`MeasuredScaledInputWidths` carries the input field bounds through threshold scaling. `MeasuredPaidSparsestRound.edge_charge` and `vertex_charge` bound the modeled work from the typed input through the tape phase. The bounds take a polynomial dominating the guarded cutoff budget, supplied by `GuardedCutoffWork.budget_polynomial`. The executable fixture exercises both original solvers and checks late exhaustion, tie handling and the free vertex branch.

The cost model still uses typed graph and vector storage. Full deterministic bit time requires a bound for the entire storage and control implementation. The refined entry starts from a nonempty graph, as do the earlier budgeted entries. The separate source dispatch handles empty graphs and the other degenerate input cases.
