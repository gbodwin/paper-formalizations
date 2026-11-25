# Paid dispatch for the budgeted sparsest-cut solvers

`MeasuredBudgetedSparsestDispatch` extends the measured typed entries to graphs of any size. The original reachability scan runs first. A disconnected request returns the empty cut. If the first scan finds no disconnected request, a second scan looks for a separable indexed request. The edge scan requires distinct endpoints. The vertex scan also requires the absence of a direct arc. These early outcomes preserve the whole tape.

`edge_value` reproduces the earlier amplified edge dispatch. `vertex_value` uses the same boundary decisions for the budgeted vertex solver, and the active branch reproduces `ConcurrentVertexBudgetRound.run`. The two completion theorems require the corresponding amplified tape budget. Each returned result specifies the original tape with a verified prefix removed. The existing comparison and probability theorems retain their demand and fair-tape hypotheses.

The charge bounds combine the measured reachability and separability scans with the reached solver work. They still use typed variables, graphs and vector storage. The executable fixture covers disconnected input, a direct request in the vertex model, and an empty graph.
