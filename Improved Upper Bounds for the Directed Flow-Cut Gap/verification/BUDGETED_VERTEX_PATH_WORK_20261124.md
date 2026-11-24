# Bounded sparsest vertex rounding and cumulative edge search work

## Vertex budgeting

`ConcurrentVertexOracle` forms a column from one binary shortest path
per demand. Only internal vertices contribute. A shared internal
vertex contributes once per path on which it appears.

The vertex covering routine uses at most (3n^2) updates for a budget
pair. Each generated pair reprices a vertex as original price divided
by the price budget, plus the reciprocal mass budget. Both budgets are
computed from the input. In the positive branch, a generated assignment
achieves normalization while keeping both original weighted price and
raw mass within 12 times the same feasible real comparator. The
selected mode and assignment attain a scale within 48 times either
comparator mode's scale. When the comparator has average demand
distance one, its raw mass equals its normalized mass.

The computed vertex cut uses the same finite fair-tape amplification as
the exact solver. The probability of exceeding twice the comparator
bound is at most (2^{-(extra+1)} + 2^{-confidence}). This comparison
assumes distinct reachable demands and at least one non-self pair
without a direct arc. If a demand can be separated by free internal
vertices, the solver returns a zero-cost cut and leaves the tape
untouched. In the remaining case every demand has a path avoiding the
free internal vertices. The full-tape completion proof returns the
unread suffix exactly.

The native fixture checks shared internal vertices, both chosen modes
and the zero-price branch on the original input and tape.

## Cumulative edge work

`ConcurrentEdgeCoverPathWork` retains the modeled binary shortest-path
charges for initialization and every reached joint-path update. It
returns exactly the prior covering state and encoded lengths. Once
the covering state stops, later scans add zero shortest-path work.

`ConcurrentEdgeBudgetPathWork` applies that measured covering routine
to every generated budget pair and returns the prior selected plan.
The exact charge sum is bounded by the candidate count times the
per-candidate bound at the verified field width. These bounds count
binary shortest-path work in the stated model. Complete structural
bit time for the deterministic phases and rounding remains open.
