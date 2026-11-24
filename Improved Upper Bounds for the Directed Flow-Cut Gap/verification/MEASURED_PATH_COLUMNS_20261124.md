# Binary path columns in the budgeted sparsest-cut solvers

`MeasuredPathMembership` compares the original vertex indices using binary arithmetic. The edge scan tests both coordinates of an arc. The vertex scan tests the two endpoints and visits the tails of the retained path in order. Both membership proofs use the actual retained path and short-circuit at the first matching arc or internal vertex.

`MeasuredPathColumn.edge_value` and `vertex_value` prove equality with the prior concurrent covering columns. A shared arc contributes one visit for every indexed demand path that traverses it. In the vertex case each path excludes its own endpoints. A missing path contributes zero. The binary summation keeps every coefficient at most the number of demand occurrences.

`MeasuredPathColumn.edge_charge` and `vertex_charge` bound the membership comparisons and binary additions for each resource and demand. The actual retained path witnesses have at most `n` edges. The bounds use `n*n` edge coordinates or `n` vertex coordinates, `m` demand occurrences, and binary widths for vertex indices and visit counts.

`MeasuredColumnCover.edgeRun_preserves` and `vertexRun_preserves` preserve the full raw covering state and its arithmetic charge. The oracle charge includes the additional column work. At budget `k`, initialization and at most `k` updates reach the oracle, so the added charge is bounded by `(k+1)` times the per-column bound. A stopped update reaches no oracle.

`MeasuredColumnBudgetSelection.edge_preserves` and `vertex_preserves` carry this accounting through all generated budget pairs and choose the same exact scored row. `MeasuredColumnSparsestRound.edge_value` and `vertex_value` return the original amplified result and unread suffix for every supplied tape. The parent approximation and finite-tape probability results apply with their existing reachability, distinctness, positive normalized-distance and tape-budget hypotheses.

The modeled charge includes path membership and column multiplicities alongside the previous optimizer arithmetic. Separate cost obligations cover free-resource detection, threshold selection, graph and vector storage, and tape execution. The proof concerns Corollary 7. It leaves the dense original-weight uniform-family horizon in Theorem 33 open.

`MeasuredColumnSparsestSmoke.lean` checks a shared arc with two path visits and a vertex column with an internal visit, endpoint exclusion and an absent path. It also checks the original edge and vertex cuts and their unread tape.
