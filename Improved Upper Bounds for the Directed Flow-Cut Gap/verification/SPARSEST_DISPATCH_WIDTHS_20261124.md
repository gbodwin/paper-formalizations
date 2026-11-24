# Original-input sparsest dispatch and covering widths

## Boundary cases of the amplified solvers

`AmplifiedSparsestDispatch.runEdge` and `runVertex` first check connectivity
in the original graph. If a demand is already disconnected, both return
an empty cut of zero sparsity and leave all tape bits unread.

If all demands are reachable, the edge branch needs a non-self demand.
The vertex branch needs a non-self demand with no direct arc. Otherwise
the entry reports that no pair can be separated by any cut, leaving the
tape intact. This covers empty demand vectors and the empty graph.
The same direct-arc demand can be separated by an edge cut.

When the input has a supported demand and all demands are reachable, the
dispatched execution is exactly the corresponding amplified solver with
its original output mask and suffix. On the stated full tape each entry
returns an outcome along with the exact unread suffix. The positive
probability bounds continue to use distinct demands.

## Widths and shortest-path charges

`MultiplicityCoverWidths.run_fits` bounds both canonical rational fields
of every actual current weight, retained normalized weight, objective,
total flow and resource load. The update factor has width at most
(2B+2U+2) when input prices fit (B) bits and column counts fit (U)
bits in the stated power-of-two bound.

`ConcurrentEdgeCoverWidths` obtains the input widths from the stored
binary price matrix and bounds the arc multiplicities by the number of
requests. It transfers the run-state bounds to the encoded output and
also handles the rational price/mass repricing.

`ConcurrentEdgeBudgetWidths` bounds the number of generated budget pairs,
their widths, the selected length matrix and the exact rational score
from the original matrix width. `ConcurrentEdgeOracleWork` retains the
binary shortest-path charges, proves it retains exactly the same demand
cells, and bounds those charges at every actual cover iteration.

The native checks include 15 generated budget pairs for original arc
price 5/7, the selected 12-bit length field and exact score 15625/117649.
They also check a measured original shortest-path call, disconnected
demands, no separating pairs, and the supported direct-arc edge round.

These proofs count the listed fields and shortest-path operations.
Complete structural bit time for the entire solver and an unrestricted
near-linear edge family at the original total weight remain open.
